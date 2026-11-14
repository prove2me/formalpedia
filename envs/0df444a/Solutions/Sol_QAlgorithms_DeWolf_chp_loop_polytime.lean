-- Prove2me | solution 1 for QAlgorithms.DeWolf.chp_loop_polytime
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:56:18.845569+00:00
-- url     : https://prove2.me/submissions/601f3b77-07c2-42c8-9157-51ab421ec9dd

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Stabilizer
import Theorems.Thm_QAlgorithms_DeWolf_chp_loop_machine
import Theorems.Thm_QAlgorithms_DeWolf_clocked_tm2_polytime
set_option autoImplicit false

/-! Reduction of QAlgorithms.DeWolf.chp_loop_polytime (e261f9b1 ChildK) to two children:
* QAlgorithms.DeWolf.chp_loop_machine: an explicit TM2 machine runs the CHP loop within (|a|+c)^d steps on valid inputs.
* QAlgorithms.DeWolf.clocked_tm2_polytime: such a machine is clocked into a total polytime function agreeing on valid inputs.
The sampler is A = (R, u). -/

open QAlgorithms QAlgorithms.Stabilizer QAlgorithms.Complexity QAlgorithms.DeWolf in
theorem solution (F : MCCFamily) : 
    let chpUpd : (n : ℕ) → CliffordOp n → Tableau n × Tableau n → Bool →
        (Tableau n × Tableau n) × Option Bool := fun n =>
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
    let simLoop : (n : ℕ) → Tableau n × Tableau n → List Bool →
        (Tableau n × Tableau n) × List (Option Bool) × List Bool := fun n s0 bits =>
      (fun st : (Tableau n × Tableau n) × List (Option Bool) × List Bool =>
        match F.ctrl n (bits.take (F.rbits.eval n)) st.2.1 with
        | none => st
        | some o => ((chpUpd n o st.1 (st.2.2.headD false)).1,
            st.2.1 ++ [(chpUpd n o st.1 (st.2.2.headD false)).2],
            match o with
            | .measure _ => st.2.2.tail
            | _ => st.2.2))^[F.steps.eval n] (s0, [], bits.drop (F.rbits.eval n))
    ∃ A : RandPolyTimeSampler, ∀ (n : ℕ) (x : Qubits n),
      F.rbits.eval n + F.steps.eval n ≤ A.rbits.eval (encInput n x).length ∧
      ∀ bits : List Bool, bits.length = A.rbits.eval (encInput n x).length →
        A.f (encInput n x ++ encBits bits) =
          encodeTableau (simLoop n
            ((fun j => ⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩ : Tableau n),
              (fun j => ⟨0, fun q => if q = j then .X else .I⟩ : Tableau n)) bits).1.1 := by
  intro chpUpd simLoop
  obtain ⟨R, hR, K, _, _, Γ, k0, k1, _, Λ, σ, _, _, _, M, main, c, d, s0, e0, e1, hrun⟩ :=
    QAlgorithms.DeWolf.chp_loop_machine F
  obtain ⟨u, hu, hcorr⟩ := QAlgorithms.DeWolf.clocked_tm2_polytime k0 k1 M main c d s0 e0 e1
    (I := Σ n : ℕ, Σ x : Qubits n, {b : List Bool // b.length = R.eval (encInput n x).length})
    (fun i => encInput i.1 i.2.1 ++ encBits i.2.2.1)
    (fun i => encodeTableau (simLoop i.1
      ((fun j => ⟨if i.2.1 j then 2 else 0, fun q => if q = j then .Z else .I⟩ : Tableau i.1),
        (fun j => ⟨0, fun q => if q = j then .X else .I⟩ : Tableau i.1)) i.2.2.1).1.1)
    (fun i => hrun i.1 i.2.1 i.2.2.1 i.2.2.2)
  exact ⟨⟨R, u, hu⟩, fun n x => ⟨hR n x, fun bits hb => hcorr ⟨n, x, bits, hb⟩⟩⟩
