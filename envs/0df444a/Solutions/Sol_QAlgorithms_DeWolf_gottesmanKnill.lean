-- Prove2me | solution 1 for QAlgorithms.DeWolf.gottesmanKnill
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:29:33.714629+00:00
-- url     : https://prove2.me/submissions/a641d1d9-b2ff-4d30-9376-4db5e01edfd6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Stabilizer
import Theorems.Thm_QAlgorithms_DeWolf_chp_update_laws
import Theorems.Thm_QAlgorithms_DeWolf_chp_loop_polytime
import Theorems.Thm_QAlgorithms_DeWolf_tableau_machine_coupling
set_option autoImplicit false

/-! e261f9b1 level-1 reduction design (session 32).
Children (to be posted with the bodies of `chpUpd` / `simLoop` INLINED as `let`s, since posted
children may not carry local defs):
* ChildQ  (Aaronson-Gottesman 2004 CHP + de Wolf pp.186-188): matrix laws of the CHP update. PROVED in
  scratch/probe/e261f9b1_gate.lean + e261f9b1_init.lean (childStepC_Q, childInit, symp_init).
* ChildK  (polytime): one sampler whose deterministic part outputs encodeTableau of the CHP loop.
  OPEN = S31 steps (a),(b) in scratch/probe/e261f9b1_K.lean + clock.lean + bridge.lean.
* ChildP  (generic probability coupling, no CHP): any state machine obeying the Q laws, driven by
  uniform bits, has the law of F.finalDist. OPEN (old S31 step (c)).
The reduction below only glues them (plus decode_encode). -/

namespace E261R
open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Complexity

/-- The CHP update on (stabilizers, destabilizers) with coin `b` (Aaronson-Gottesman 2004, Sec. III). -/
def chpUpd (n : ℕ) : CliffordOp n → Tableau n × Tableau n → Bool → (Tableau n × Tableau n) × Option Bool :=
  let px : Pauli → Bool := fun | .I => false | .X => true | .Y => true | .Z => false
  let pz : Pauli → Bool := fun | .I => false | .X => false | .Y => true | .Z => true
  let conjH : Pauli → ZMod 4 × Pauli := fun | .I => (0, .I) | .X => (0, .Z) | .Y => (2, .Y) | .Z => (0, .X)
  let conjS : Pauli → ZMod 4 × Pauli := fun | .I => (0, .I) | .X => (0, .Y) | .Y => (2, .X) | .Z => (0, .Z)
  let conjP : Pauli → Pauli → ZMod 4 × Pauli := fun P Q => (if P = .I ∨ Q = .I ∨ P = Q then 0 else 2, Q)
  let conjPS : (Pauli → ZMod 4 × Pauli) → Fin n → PauliString n → PauliString n := fun f q P =>
    ⟨P.phase + (f (P.ops q)).1, Function.update P.ops q (f (P.ops q)).2⟩
  let cnotTab : Pauli → Pauli → ZMod 4 × Pauli × Pauli := fun Pc Pt =>
    (if px Pc && pz Pt && (px Pt == pz Pc) then 2 else 0,
      pauliOfBits (px Pc) (xor (pz Pc) (pz Pt)), pauliOfBits (xor (px Pt) (px Pc)) (pz Pt))
  let cnotPS : Fin n → Fin n → PauliString n → PauliString n := fun c t P =>
    ⟨P.phase + (cnotTab (P.ops c) (P.ops t)).1,
      Function.update (Function.update P.ops c (cnotTab (P.ops c) (P.ops t)).2.1) t
        (cnotTab (P.ops c) (P.ops t)).2.2⟩
  let updG : CliffordOp n → Tableau n → Tableau n := fun op T =>
    match op with
    | .pauli q P => fun j => conjPS (conjP P) q (T j)
    | .h q => fun j => conjPS conjH q (T j)
    | .s q => fun j => conjPS conjS q (T j)
    | .cnot c t _ => fun j => cnotPS c t (T j)
    | .measure _ => T
  let antiPair : Pauli → Pauli → Bool := fun a b => decide (a ≠ .I ∧ b ≠ .I ∧ a ≠ b)
  let antiB : PauliString n → PauliString n → Bool := fun P Q =>
    decide (Odd (Finset.univ.filter fun q => antiPair (P.ops q) (Q.ops q) = true).card)
  let oneP : PauliString n := ⟨0, fun _ => .I⟩
  let prodSel : (Fin n → PauliString n) → Finset (Fin n) → PauliString n := fun T s =>
    (List.ofFn fun i => if i ∈ s then T i else oneP).foldr PauliString.mul oneP
  let firstAnti : Tableau n → (Fin n → Pauli) → Option (Fin n) := fun T M =>
    (List.finRange n).reverse.find? (fun j => antiB (T j) ⟨0, M⟩)
  let detSel : Tableau n → (Fin n → Pauli) → Finset (Fin n) := fun D M =>
    Finset.univ.filter fun j => antiB (D j) ⟨0, M⟩ = true
  let updM : Tableau n → (Fin n → Pauli) → Fin n → Bool → Tableau n := fun T M p b =>
    fun j => if j = p then ⟨if b then 2 else 0, M⟩
      else if antiB (T j) ⟨0, M⟩ then (T j).mul (T p) else T j
  let updDM : Tableau n → Tableau n → (Fin n → Pauli) → Fin n → Tableau n := fun T D M p =>
    fun i => if i = p then T p else if antiB (D i) ⟨0, M⟩ then (D i).mul (T p) else D i
  fun op TD b =>
    match op with
    | .measure M =>
      match firstAnti TD.1 M with
      | some p => ((updM TD.1 M p b, updDM TD.1 TD.2 M p), some b)
      | none => (TD, some (decide ((prodSel TD.1 (detSel TD.2 M)).phase = 2)))
    | _ => ((updG op TD.1, updG op TD.2), none)

/-- Run the controller of `F` for `steps(n)` rounds: random bits `r` = first `rbits(n)` bits,
measurement coins = the remaining bits, one fresh coin per measurement. -/
def simLoop {σ : Type} (F : MCCFamily) (n : ℕ) (upd : CliffordOp n → σ → Bool → σ × Option Bool)
    (s0 : σ) (bits : List Bool) : σ × List (Option Bool) × List Bool :=
  (fun st : σ × List (Option Bool) × List Bool =>
    match F.ctrl n (bits.take (F.rbits.eval n)) st.2.1 with
    | none => st
    | some o => ((upd o st.1 (st.2.2.headD false)).1, st.2.1 ++ [(upd o st.1 (st.2.2.headD false)).2],
        match o with
        | .measure _ => st.2.2.tail
        | _ => st.2.2))^[F.steps.eval n] (s0, [], bits.drop (F.rbits.eval n))

/-- The projector onto the `β` eigenspace of the Pauli string `M`. -/
noncomputable abbrev projM {n : ℕ} (M : Fin n → Pauli) (β : Bool) : Matrix (Qubits n) (Qubits n) ℂ :=
  (2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • (PauliString.toMatrix ⟨0, M⟩))

/-- Q laws of a state machine (`tab` reads the stabilizer tableau of a state). -/
def QLaws {n : ℕ} {σ : Type} (upd : CliffordOp n → σ → Bool → σ × Option Bool)
    (tab : σ → Tableau n) (Inv : σ → Prop) : Prop :=
  (∀ op s b, Inv s → Inv (upd op s b).1) ∧
  (∀ s, Inv s → IsValidTableau (tab s)) ∧
  (∀ (op : CliffordOp n) s b, Inv s → (∀ M, op ≠ .measure M) →
      (upd op s b).2 = none ∧
      tableauProjector (tab (upd op s b).1) = op.mat * tableauProjector (tab s) * op.mat.conjTranspose) ∧
  (∀ (M : Fin n → Pauli) s b, Inv s →
    ∃ β, (upd (.measure M) s b).2 = some β ∧
      (((projM M β * tableauProjector (tab s)).trace = 1 ∧
          ∀ b', upd (.measure M) s b' = upd (.measure M) s b) ∨
        ((projM M true * tableauProjector (tab s)).trace = 2⁻¹ ∧ β = b)) ∧
      tableauProjector (tab (upd (.measure M) s b).1) =
        (projM M β * tableauProjector (tab s)).trace⁻¹ •
          (projM M β * tableauProjector (tab s) * projM M β))

/-- ChildQ: CHP correctness at the matrix level, with an invariant (validity + symplectic destabilizers). -/
def ChildQ : Prop :=
  ∃ Inv : (n : ℕ) → Tableau n × Tableau n → Prop, ∀ n : ℕ,
    (∀ x : Qubits n,
      Inv n ((fun j => ⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩ : Tableau n),
        (fun j => ⟨0, fun q => if q = j then .X else .I⟩ : Tableau n)) ∧
      tableauProjector (fun j => ⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩ : Tableau n) =
        pureDensity (ket x)) ∧
    QLaws (chpUpd n) Prod.fst (Inv n)

/-- ChildK: the CHP simulation loop is computed by one randomized polynomial-time sampler. -/
def ChildK : Prop :=
  ∀ F : MCCFamily, ∃ A : RandPolyTimeSampler, ∀ (n : ℕ) (x : Qubits n),
    F.rbits.eval n + F.steps.eval n ≤ A.rbits.eval (encInput n x).length ∧
    ∀ bits : List Bool, bits.length = A.rbits.eval (encInput n x).length →
      A.f (encInput n x ++ encBits bits) =
        encodeTableau (simLoop F n (chpUpd n)
          ((fun j => ⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩ : Tableau n),
            (fun j => ⟨0, fun q => if q = j then .X else .I⟩ : Tableau n)) bits).1.1

/-- ChildP: generic coupling. A state machine obeying the Q laws, driven by uniform bits,
reproduces the law of the circuit's final density matrix. -/
def ChildP : Prop :=
  ∀ (F : MCCFamily) (n : ℕ) (x : Qubits n) (σ : Type) (upd : CliffordOp n → σ → Bool → σ × Option Bool)
    (tab : σ → Tableau n) (Inv : σ → Prop) (s0 : σ),
    Inv s0 → tableauProjector (tab s0) = pureDensity (ket x) → QLaws upd tab Inv →
    ∀ m : ℕ, F.rbits.eval n + F.steps.eval n ≤ m →
      (∀ bits : List Bool, Inv (simLoop F n upd s0 bits).1) ∧
      (PMF.uniformOfFintype (Fin m → Bool)).map
          (fun bits => tableauProjector (tab (simLoop F n upd s0 (List.ofFn bits)).1)) =
        F.finalDist n x

/-! ### Reduction glue -/

def initTD (n : ℕ) (x : Qubits n) : Tableau n × Tableau n :=
  ((fun j => ⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩ : Tableau n),
    (fun j => ⟨0, fun q => if q = j then .X else .I⟩ : Tableau n))

lemma getD_flatten_ofFn {α : Type} {k : ℕ} : ∀ {m : ℕ} (f : Fin m → List α), (∀ j, (f j).length = k) →
    ∀ (j : Fin m) (i : ℕ), i < k → ∀ d : α,
      ((List.ofFn f).flatten).getD (j * k + i) d = (f j).getD i d
  | 0, _, _, j, _, _, _ => j.elim0
  | m + 1, f, hf, j, i, hi, d => by
    rw [List.ofFn_succ, List.flatten_cons]
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · simp only [Fin.val_zero, zero_mul, zero_add, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by rw [hf]; exact hi)]
    · have h1 : (f 0).length ≤ (j'.succ : ℕ) * k + i := by
        rw [hf 0, Fin.val_succ]; nlinarith
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h1, ← List.getD_eq_getElem?_getD]
      have h2 : (j'.succ : ℕ) * k + i - (f 0).length = j' * k + i := by
        rw [hf 0, Fin.val_succ, add_mul, one_mul]; omega
      rw [h2]
      exact getD_flatten_ofFn (fun j => f j.succ) (fun j => hf _) j' i hi d

lemma phase_dec (c : ZMod 4) :
    (if (encPhase c).getD 0 false then (2 : ZMod 4) else 0) + (if (encPhase c).getD 1 false then 1 else 0) = c := by
  revert c; decide

lemma pauli_dec (P : Pauli) : pauliOfBits ((encPauli P).getD 0 false) ((encPauli P).getD 1 false) = P := by
  cases P <;> rfl

theorem decode_encode {n : ℕ} (T : Tableau n) : decodeTableau n (encodeTableau T) = T := by
  funext j
  have hlen : ∀ j : Fin n, (encPhase (T j).phase ++
      (List.ofFn fun q => encPauli ((T j).ops q)).flatten).length = 2 * n + 2 := by
    intro j
    have : ∀ P : Pauli, (encPauli P).length = 2 := fun P => by cases P <;> rfl
    simp [encPhase, List.length_flatten, this, List.sum_ofFn]; ring
  have hops : ∀ (q : Fin n) (i : ℕ), i < 2 →
      ((List.ofFn fun q => encPauli ((T j).ops q)).flatten).getD (q * 2 + i) false =
        (encPauli ((T j).ops q)).getD i false :=
    fun q i hi => getD_flatten_ofFn _ (fun q => by cases (T j).ops q <;> rfl) q i hi false
  have hblk : ∀ i, i < 2 * n + 2 → (encodeTableau T).getD (j * (2 * n + 2) + i) false =
      (encPhase (T j).phase ++ (List.ofFn fun q => encPauli ((T j).ops q)).flatten).getD i false :=
    fun i hi => getD_flatten_ofFn _ hlen j i hi false
  rcases hT : T j with ⟨c, o⟩
  simp only [decodeTableau]
  congr 1
  · rw [show j * (2 * n + 2) = j * (2 * n + 2) + 0 by rfl, hblk 0 (by omega), hblk 1 (by omega), hT]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (show 0 < (encPhase c).length by simp [encPhase]),
      List.getElem?_append_left (show 1 < (encPhase c).length by simp [encPhase])]
    simpa [List.getD_eq_getElem?_getD] using phase_dec c
  · funext q
    have e1 : j * (2 * n + 2) + 2 + 2 * q = j * (2 * n + 2) + (2 + (q * 2 + 0)) := by ring
    have e2 : j * (2 * n + 2) + 3 + 2 * q = j * (2 * n + 2) + (2 + (q * 2 + 1)) := by ring
    have hpl : (encPhase (T j).phase).length = 2 := by simp [encPhase]
    have happ : ∀ i' : ℕ, (encPhase (T j).phase ++ (List.ofFn fun q => encPauli ((T j).ops q)).flatten).getD
        (2 + i') false = ((List.ofFn fun q => encPauli ((T j).ops q)).flatten).getD i' false := by
      intro i'
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hpl]; omega), hpl,
        Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
    have hq := q.isLt
    rw [e1, e2, hblk _ (by omega), hblk _ (by omega), happ, happ, hops q 0 (by omega),
      hops q 1 (by omega), pauli_dec, hT]

theorem reduction (hQ : ChildQ) (hK : ChildK) (hP : ChildP) (F : MCCFamily) :
    ∃ A : RandPolyTimeSampler, ∀ (n : ℕ) (x : Qubits n),
      (∀ s ∈ (A.outDist (encInput n x)).support,
          ∃ T : Tableau n, IsValidTableau T ∧ s = encodeTableau T) ∧
        (A.outDist (encInput n x)).map (fun s => tableauProjector (decodeTableau n s)) =
          F.finalDist n x := by
  obtain ⟨Inv, hQ⟩ := hQ
  obtain ⟨A, hA⟩ := hK F
  refine ⟨A, fun n x => ?_⟩
  obtain ⟨hm, hf⟩ := hA n x
  obtain ⟨hI0, hP0⟩ := (hQ n).1 x
  have hL := (hQ n).2
  obtain ⟨hInv, hdist⟩ := hP F n x _ (chpUpd n) Prod.fst (Inv n) (initTD n x) hI0 hP0 hL _ hm
  have hout : A.outDist (encInput n x) = (PMF.uniformOfFintype _).map
      (fun r : Fin (A.rbits.eval (encInput n x).length) → Bool =>
        encodeTableau (simLoop F n (chpUpd n) (initTD n x) (List.ofFn r)).1.1) := by
    unfold RandPolyTimeSampler.outDist
    congr 1
    funext r
    exact hf _ (List.length_ofFn)
  refine ⟨?_, ?_⟩
  · intro s hs
    rw [hout, PMF.support_map] at hs
    obtain ⟨r, _, rfl⟩ := hs
    exact ⟨_, hL.2.1 _ (hInv _), rfl⟩
  · rw [hout, PMF.map_comp]
    simp only [Function.comp_def, decode_encode]
    exact hdist

end E261R

open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Complexity in
theorem solution (F : MCCFamily) :
    ∃ A : RandPolyTimeSampler, ∀ (n : ℕ) (x : Qubits n),
      (∀ s ∈ (A.outDist (encInput n x)).support,
          ∃ T : Tableau n, IsValidTableau T ∧ s = encodeTableau T) ∧
        (A.outDist (encInput n x)).map (fun s => tableauProjector (decodeTableau n s)) =
          F.finalDist n x := by
  exact E261R.reduction QAlgorithms.DeWolf.chp_update_laws
    (fun F => QAlgorithms.DeWolf.chp_loop_polytime F)
    (fun F n x σ upd tab Inv s0 h0 hx hL m hm =>
      QAlgorithms.DeWolf.tableau_machine_coupling F n x σ upd tab Inv s0 h0 hx
        hL.1 hL.2.1 hL.2.2.1 hL.2.2.2 m hm) F
