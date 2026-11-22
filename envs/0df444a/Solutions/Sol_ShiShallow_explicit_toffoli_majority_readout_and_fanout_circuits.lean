-- Prove2me | solution 1 for ShiShallow.explicit_toffoli_majority_readout_and_fanout_circuits
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-18T06:20:39.672922+00:00
-- url     : https://prove2.me/submissions/f1b176ab-f9e6-4898-908a-1c9208e9ba4d

/-
EXPLICIT-1.  The amplifier's Toffoli and majority-readout circuits as LITERAL TERMS.

`ShiShallow.exists_toffoli_at_wires_layerOk_depth` and
`ShiShallow.exists_majority_readout_at_wires_layerOk_depth` pin their circuits only
BEHAVIOURALLY, so a machine that must EMIT one of them (the `Uniform` obligation) has no
syntactic handle on it.  This file replaces both existence statements with the same
conclusions carried by a circuit the reader can see: an explicit `Layered N`, one gate per
layer, spelled out in the statement of `theorem solution`.

Contents of the statement, all four conjuncts carrying explicit circuits:

  1. TOFFOLI at arbitrary distinct `p q r : Fin N`: the 37-layer list, its action
     `x r |-> x r ^^^ (x p && x q)`, `LayerOk` on every layer, `depth = 37`.
  2. MAJORITY READOUT at arbitrary `w1 w2 w3 s : Fin N`: the concatenation of the three
     explicit Toffoli blocks `(w1,w2;s)`, `(w2,w3;s)`, `(w1,w3;s)`, its action
     `x s |-> x s ^^^ ((w1&&w2) ^^^ (w2&&w3) ^^^ (w1&&w3))`, `LayerOk`, `depth = 111`.
     The depth arithmetic is literally `37 + 37 + 37 = 111`.
  3. FAN-OUT on `Fin (n + n)`: the one-layer CNOT ladder
     `[(List.finRange n).map (fun j => Instr.cnot (castAdd n j) (natAdd n j) _)]`, its
     `Fin.addCases` action, `LayerOk`, `depth = 1`.  The CNOT's distinctness side condition
     is given as an inline PROOF TERM, so no private name enters the statement.
  4. A CONCRETE, UNCONDITIONAL CHECK of conjunct 1 at `N = 3`, `p q r = 0 1 2`, at four
     literal basis strings: the pullback sends `110 |-> 111` and `111 |-> 110` (both
     controls set, target flips) and fixes `100` and `011` (a control missing).

NO TRANSPORT FROM `QState 3` IS NEEDED, and that is the main finding.  The hard quantum
content -- `ShiShallow.apply1_tMat_eq_phase`, `ShiShallow.cnot_conj_phase_map`,
`ShiShallow.phase_composition`, `ShiShallow.ccz_phase_exponent_eq`,
`ShiShallow.inv_sqrt_two_mul_self` -- is ALREADY STATED AT ARBITRARY `n` and arbitrary
wires.  `ShiShallow.ccz_circuit_eq_phase` is the `QState 3` packaging of exactly these
five, so the CCZ phase algebra is redone at `p q r : Fin N` from the same inputs instead of
being transported: the diagonal-phase blocks compose at general wires with no reindexing
lemma, no `Fin.addCases` cast and no bijectivity hypothesis.  `ShiSpread`/`ShiEmbed` are
therefore not imported at all.

The Hadamard conjugation (`toffoli_from_ccz_hadamard_conj`, also a `QState 3` statement) is
likewise redone at `r : Fin N`; `inv_sqrt_two_mul_self` is the only arithmetic input.

`ShiShallow.runLayered_append_action_readout` is the one structural lemma used, for the
three-block concatenation in conjunct 2.
-/
import Definitions.Def_ShiShallow_Core
import Theorems.Thm_ShiShallow_apply1_tMat_eq_phase
import Theorems.Thm_ShiShallow_cnot_conj_phase_map
import Theorems.Thm_ShiShallow_phase_composition
import Theorems.Thm_ShiShallow_ccz_phase_exponent_eq
import Theorems.Thm_ShiShallow_inv_sqrt_two_mul_self
import Theorems.Thm_ShiShallow_runLayered_append_action_readout

set_option autoImplicit false

open ShiShallow

/-! ## Diagonal-phase calculus at arbitrary wires of an arbitrary register -/

/-- `shiTof_Ph F a`: `F` acts as multiplication by the diagonal phase `a`. -/
private abbrev shiTof_Ph {N : ℕ} (F : QState N → QState N) (a : Bits N → ℂ) : Prop :=
  ∀ (φ : QState N) (x : Bits N), F φ x = a x * φ x

private lemma shiTof_Ph_comp {N : ℕ} {f g : QState N → QState N} {a b : Bits N → ℂ}
    (hf : shiTof_Ph f a) (hg : shiTof_Ph g b) :
    shiTof_Ph (fun ψ => g (f ψ)) (fun x => b x * a x) := by
  intro ψ x
  exact phase_composition f g a b hf hg ψ x

private lemma shiTof_Ph_conj {N : ℕ} {F : QState N → QState N} {a : Bits N → ℂ}
    (i j : Fin N) (hij : i ≠ j) (hF : shiTof_Ph F a) :
    shiTof_Ph (fun ψ => cnotState i j hij (F (cnotState i j hij ψ)))
      (fun x => a (Function.update x j (xor (x j) (x i)))) := by
  intro ψ x
  exact congrFun (cnot_conj_phase_map i j hij ψ F a hF) x

private lemma shiTof_Ph_t {N : ℕ} (i : Fin N) :
    shiTof_Ph (apply1 tMat i)
      (fun x => if x i then Complex.exp (Complex.I * Real.pi / 4) else 1) := by
  intro φ x
  simp only [apply1_tMat_eq_phase]

/-- `T ^ 7` on one wire, as seven `T` gates -- the `Instr` alphabet has no `T`-inverse
letter, and this is where seven of the thirty-seven layers come from. -/
private noncomputable def shiTof_T7 {N : ℕ} (i : Fin N) (ψ : QState N) : QState N :=
  apply1 tMat i (apply1 tMat i (apply1 tMat i (apply1 tMat i
    (apply1 tMat i (apply1 tMat i (apply1 tMat i ψ))))))

private lemma shiTof_Ph_T7 {N : ℕ} (i : Fin N) :
    shiTof_Ph (shiTof_T7 i)
      (fun x => if x i then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) := by
  intro φ x
  simp only [shiTof_T7, apply1_tMat_eq_phase]
  cases hx : x i with
  | false => simp [hx]
  | true =>
      simp only [hx, if_true]
      ring

/-- A `T^7` block conjugated by a CNOT: control `i`, target `j`. -/
private noncomputable def shiTof_cB {N : ℕ} (i j : Fin N) (hij : i ≠ j) (ψ : QState N) :
    QState N :=
  cnotState i j hij (shiTof_T7 j (cnotState i j hij ψ))

private lemma shiTof_Ph_cB {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    shiTof_Ph (shiTof_cB i j hij)
      (fun x => if xor (x j) (x i) then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) := by
  intro φ x
  have h := shiTof_Ph_conj i j hij (shiTof_Ph_T7 j) φ x
  simp only [Function.update_self] at h
  exact h

/-- The three-parity `T` block: `CNOT(p,r) CNOT(q,r) T_r CNOT(q,r) CNOT(p,r)`. -/
private noncomputable def shiTof_cB7 {N : ℕ} (p q r : Fin N) (hpr : p ≠ r) (hqr : q ≠ r)
    (ψ : QState N) : QState N :=
  cnotState p r hpr (cnotState q r hqr (apply1 tMat r
    (cnotState q r hqr (cnotState p r hpr ψ))))

private lemma shiTof_Ph_cB7 {N : ℕ} (p q r : Fin N) (hpr : p ≠ r) (hqr : q ≠ r) :
    shiTof_Ph (shiTof_cB7 p q r hpr hqr)
      (fun x => if xor (xor (x r) (x p)) (x q) then
        Complex.exp (Complex.I * Real.pi / 4) else 1) := by
  intro φ x
  have h := shiTof_Ph_conj p r hpr (shiTof_Ph_conj q r hqr (shiTof_Ph_t r)) φ x
  simp only [Function.update_self, Function.update_of_ne hqr] at h
  exact h

/-- The seven block phases multiply to the CCZ sign. -/
private lemma shiTof_phase_prod (a b c : Bool) :
    (if xor (xor c a) b then Complex.exp (Complex.I * Real.pi / 4) else 1) *
      ((if xor c a then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) *
        ((if xor c b then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) *
          ((if xor b a then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) *
            ((if c then Complex.exp (Complex.I * Real.pi / 4) else 1) *
              ((if b then Complex.exp (Complex.I * Real.pi / 4) else 1) *
                (if a then Complex.exp (Complex.I * Real.pi / 4) else 1))))))
      = if a && b && c then (-1 : ℂ) else 1 := by
  have h := ccz_phase_exponent_eq a b c
  cases a <;> cases b <;> cases c <;>
    first
      | (norm_num at h ⊢; done)
      | (norm_num at h ⊢; linear_combination h)
      | (norm_num; done)
      | linear_combination h

/-- The CCZ part of the circuit, as a composition of the seven diagonal blocks, AT
ARBITRARY WIRES.  This is the step that would otherwise need a transport law out of
`QState 3`: there is none, and none is needed. -/
private noncomputable def shiTof_cczOp {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (ψ : QState N) : QState N :=
  shiTof_cB7 p q r hpr hqr (shiTof_cB p r hpr (shiTof_cB q r hqr (shiTof_cB p q hpq
    (apply1 tMat r (apply1 tMat q (apply1 tMat p ψ))))))

private lemma shiTof_Ph_ccz {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    shiTof_Ph (shiTof_cczOp p q r hpq hpr hqr)
      (fun x => if x p && x q && x r then (-1 : ℂ) else 1) := by
  have c7 := shiTof_Ph_comp (shiTof_Ph_comp (shiTof_Ph_comp (shiTof_Ph_comp
      (shiTof_Ph_comp (shiTof_Ph_comp (shiTof_Ph_t p) (shiTof_Ph_t q)) (shiTof_Ph_t r))
      (shiTof_Ph_cB p q hpq)) (shiTof_Ph_cB q r hqr)) (shiTof_Ph_cB p r hpr))
      (shiTof_Ph_cB7 p q r hpr hqr)
  intro φ x
  first
    | exact (c7 φ x).trans
        (congrArg (fun z : ℂ => z * φ x) (shiTof_phase_prod (x p) (x q) (x r)))
    | (refine (c7 φ x).trans ?_
       rw [← shiTof_phase_prod (x p) (x q) (x r)])
    | (refine (c7 φ x).trans ?_
       beta_reduce
       rw [shiTof_phase_prod (x p) (x q) (x r)])

/-! ### `H_r . CCZ . H_r = Toffoli` at general wires -/

private lemma shiTof_hconj {N : ℕ} (p q r : Fin N) (hpr : p ≠ r) (hqr : q ≠ r)
    (F : QState N → QState N)
    (hF : ∀ (φ : QState N) (y : Bits N),
      F φ y = (if y p && y q && y r then (-1 : ℂ) else 1) * φ y)
    (ψ : QState N) :
    apply1 hMat r (F (apply1 hMat r ψ))
      = fun x => ψ (Function.update x r (xor (x r) (x p && x q))) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 :=
    ShiShallow.inv_sqrt_two_mul_self
  funext x
  have hup : ∀ b : Bool, F (apply1 hMat r ψ) (Function.update x r b)
      = (if x p && x q && b then (-1 : ℂ) else 1)
        * ∑ c : Bool, hMat b c * ψ (Function.update x r c) := by
    intro b
    have e1 : Function.update x r b p = x p := Function.update_of_ne hpr b x
    have e2 : Function.update x r b q = x q := Function.update_of_ne hqr b x
    have e3 : Function.update x r b r = b := Function.update_self r b x
    have e4 : apply1 hMat r ψ (Function.update x r b)
        = ∑ c : Bool, hMat b c * ψ (Function.update x r c) := by
      simp only [apply1, Function.update_self, Function.update_idem]
    simp only [hF, e1, e2, e3, e4]
  have main : apply1 hMat r (F (apply1 hMat r ψ)) x
      = ∑ b : Bool, hMat (x r) b * F (apply1 hMat r ψ) (Function.update x r b) := rfl
  rw [main]
  -- PHASE 1: split the outer Bool sum, `hMat` still FOLDED.
  simp only [Fintype.sum_bool]
  -- PHASE 2: expand `F` while `hMat` is still folded, so `hup`'s LHS still matches.
  first
    | rw [hup true, hup false]
    | simp only [hup]
  -- PHASE 3: only now unfold the matrix and split the two inner Bool sums.
  simp only [hMat, Matrix.of_apply, Fintype.sum_bool]
  -- PHASE 4: abstract the irrational AFTER all unfolding.
  set s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ with hsdef
  cases hr : x r <;> cases hm : (x p && x q) <;> (try simp only [hr, hm]) <;> norm_num <;>
    first
      | linear_combination (2 * ψ (Function.update x r false)) * hs
      | linear_combination (2 * ψ (Function.update x r true)) * hs
      | linear_combination (-2 * ψ (Function.update x r false)) * hs
      | linear_combination (-2 * ψ (Function.update x r true)) * hs

/-! ## The explicit 37-gate list and its layering -/

/-- The 37 gates, in time order: `H_r`, the CCZ sequence at `p,q,r`, `H_r`. -/
private def shiTof_gates {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    List (Instr N) :=
  [Instr.h r, Instr.t p, Instr.t q, Instr.t r, Instr.cnot p q hpq, Instr.t q, Instr.t q,
   Instr.t q, Instr.t q, Instr.t q, Instr.t q, Instr.t q, Instr.cnot p q hpq,
   Instr.cnot q r hqr, Instr.t r, Instr.t r, Instr.t r, Instr.t r, Instr.t r, Instr.t r,
   Instr.t r, Instr.cnot q r hqr, Instr.cnot p r hpr, Instr.t r, Instr.t r, Instr.t r,
   Instr.t r, Instr.t r, Instr.t r, Instr.t r, Instr.cnot p r hpr, Instr.cnot p r hpr,
   Instr.cnot q r hqr, Instr.t r, Instr.cnot q r hqr, Instr.cnot p r hpr, Instr.h r]

private lemma shiTof_layerOk_map {N : ℕ} (gs : List (Instr N)) :
    ∀ l ∈ gs.map (fun g => [g]), LayerOk l := by
  intro l hl
  simp only [List.mem_map] at hl
  obtain ⟨g, _, hg⟩ := hl
  subst hg
  exact List.pairwise_singleton _ g

private lemma shiTof_run_map {N : ℕ} (gs : List (Instr N)) (ψ : QState N) :
    runLayered (gs.map (fun g => [g])) ψ = gs.foldl (fun st g => Instr.apply g st) ψ := by
  induction gs generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
      have hstep : runLayered ((g :: gs).map (fun z => [z])) ψ
          = runLayered (gs.map (fun z => [z])) (Instr.apply g ψ) := rfl
      rw [hstep, ih, List.foldl_cons]

private lemma shiTof_fold_eq {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (ψ : QState N) :
    (shiTof_gates p q r hpq hpr hqr).foldl (fun st g => Instr.apply g st) ψ
      = apply1 hMat r (shiTof_cczOp p q r hpq hpr hqr (apply1 hMat r ψ)) := by
  first
    | rfl
    | simp only [shiTof_gates, shiTof_cczOp, shiTof_cB, shiTof_cB7, shiTof_T7,
        List.foldl_cons, List.foldl_nil, Instr.apply]

/-- One gate per layer, so each layer is a singleton. -/
private abbrev shiE_T {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Layered N := (shiTof_gates p q r hpq hpr hqr).map (fun g => [g])

/-- The full Toffoli specification at the EXPLICIT circuit. -/
private theorem shiE_tof_spec {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) :
    (∀ ψ : QState N, runLayered ((shiTof_gates p q r hpq hpr hqr).map (fun g => [g])) ψ
        = fun x => ψ (Function.update x r (xor (x r) (x p && x q))))
      ∧ (∀ l ∈ (shiTof_gates p q r hpq hpr hqr).map (fun g => [g]), LayerOk l)
      ∧ depth ((shiTof_gates p q r hpq hpr hqr).map (fun g => [g])) = 37 := by
  refine ⟨?_, ?_, ?_⟩
  · intro ψ
    rw [shiTof_run_map, shiTof_fold_eq]
    exact shiTof_hconj p q r hpr hqr (shiTof_cczOp p q r hpq hpr hqr)
      (fun φ y => shiTof_Ph_ccz p q r hpq hpr hqr φ y) ψ
  · exact shiTof_layerOk_map _
  · first
      | rfl
      | simp [depth, shiTof_gates]

/-! ## The majority readout: three explicit Toffoli blocks concatenated -/

/-- Reassociating the accumulated XOR.  `d` is the incoming scratch bit; the three Toffolis
contribute `c`, then `b`, then `a`, so the accumulation is left-nested in the reverse of the
stated order. -/
private theorem shiMR_xor_rearrange (d a b c : Bool) :
    xor (xor (xor d c) b) a = xor d (xor (xor a b) c) := by
  first
    | (cases d <;> cases a <;> cases b <;> cases c <;> rfl)
    | (decide +revert)

private abbrev shiE_R {N : ℕ} (w1 w2 w3 s : Fin N) (h12 : w1 ≠ w2) (h13 : w1 ≠ w3)
    (h23 : w2 ≠ w3) (h1s : w1 ≠ s) (h2s : w2 ≠ s) (h3s : w3 ≠ s) : Layered N :=
  (shiE_T w1 w2 s h12 h1s h2s ++ shiE_T w2 w3 s h23 h2s h3s) ++ shiE_T w1 w3 s h13 h1s h3s

private theorem shiE_read_spec {N : ℕ} (w1 w2 w3 s : Fin N) (h12 : w1 ≠ w2) (h13 : w1 ≠ w3)
    (h23 : w2 ≠ w3) (h1s : w1 ≠ s) (h2s : w2 ≠ s) (h3s : w3 ≠ s) :
    (∀ ψ : QState N, runLayered (shiE_R w1 w2 w3 s h12 h13 h23 h1s h2s h3s) ψ
        = fun x => ψ (Function.update x s
            (xor (x s) (xor (xor (x w1 && x w2) (x w2 && x w3)) (x w1 && x w3)))))
      ∧ (∀ l ∈ shiE_R w1 w2 w3 s h12 h13 h23 h1s h2s h3s, LayerOk l)
      ∧ depth (shiE_R w1 w2 w3 s h12 h13 h23 h1s h2s h3s) = 111 := by
  obtain ⟨hc12, hok12, hd12⟩ := shiE_tof_spec w1 w2 s h12 h1s h2s
  obtain ⟨hc23, hok23, hd23⟩ := shiE_tof_spec w2 w3 s h23 h2s h3s
  obtain ⟨hc13, hok13, hd13⟩ := shiE_tof_spec w1 w3 s h13 h1s h3s
  refine ⟨?_, ?_, ?_⟩
  · intro ψ
    have hstep1 : ∀ χ : QState N,
        runLayered (shiE_T w1 w2 s h12 h1s h2s ++ shiE_T w2 w3 s h23 h2s h3s) χ
          = fun x => runLayered (shiE_T w1 w2 s h12 h1s h2s) χ
              (Function.update x s (xor (x s) (x w2 && x w3))) := by
      intro χ
      exact ShiShallow.runLayered_append_action_readout
        (shiE_T w1 w2 s h12 h1s h2s) (shiE_T w2 w3 s h23 h2s h3s)
        (fun ρ => runLayered (shiE_T w1 w2 s h12 h1s h2s) ρ)
        (fun x => Function.update x s (xor (x s) (x w2 && x w3)))
        (fun _ => rfl) hc23 χ
    have hstep2 : runLayered (shiE_R w1 w2 w3 s h12 h13 h23 h1s h2s h3s) ψ
        = fun x => runLayered (shiE_T w1 w2 s h12 h1s h2s ++ shiE_T w2 w3 s h23 h2s h3s) ψ
            (Function.update x s (xor (x s) (x w1 && x w3))) :=
      ShiShallow.runLayered_append_action_readout
        (shiE_T w1 w2 s h12 h1s h2s ++ shiE_T w2 w3 s h23 h2s h3s)
        (shiE_T w1 w3 s h13 h1s h3s)
        (fun ρ => runLayered (shiE_T w1 w2 s h12 h1s h2s ++ shiE_T w2 w3 s h23 h2s h3s) ρ)
        (fun x => Function.update x s (xor (x s) (x w1 && x w3)))
        (fun _ => rfl) hc13 ψ
    rw [hstep2, hstep1 ψ, hc12]
    funext x
    (try dsimp only)
    have e1 : ∀ v : Bool, Function.update x s v w1 = x w1 :=
      fun v => Function.update_of_ne h1s v x
    have e2 : ∀ v : Bool, Function.update x s v w2 = x w2 :=
      fun v => Function.update_of_ne h2s v x
    have e3 : ∀ v : Bool, Function.update x s v w3 = x w3 :=
      fun v => Function.update_of_ne h3s v x
    have es : ∀ v : Bool, Function.update x s v s = v :=
      fun v => Function.update_self s v x
    have eid : ∀ u v : Bool,
        Function.update (Function.update x s u) s v = Function.update x s v :=
      fun u v => Function.update_idem u v x
    simp only [e1, e2, e3, es, eid]
    all_goals
      first
        | (rfl; done)
        | (rw [shiMR_xor_rearrange]; done)
        | (exact congrArg ψ (congrArg (Function.update x s)
              (shiMR_xor_rearrange (x s) (x w1 && x w2) (x w2 && x w3) (x w1 && x w3))); done)
  · intro l hl
    rcases List.mem_append.mp hl with hl1 | hl1
    · rcases List.mem_append.mp hl1 with hl2 | hl2
      · exact hok12 l hl2
      · exact hok23 l hl2
    · exact hok13 l hl1
  · have e12 : (shiE_T w1 w2 s h12 h1s h2s).length = 37 := hd12
    have e23 : (shiE_T w2 w3 s h23 h2s h3s).length = 37 := hd23
    have e13 : (shiE_T w1 w3 s h13 h1s h3s).length = 37 := hd13
    show (shiE_R w1 w2 w3 s h12 h13 h23 h1s h2s h3s).length = 111
    simp only [shiE_R, List.length_append, e12, e23, e13]

/-! ## The fan-out layer on `Fin (n + n)`

`(Fin.castAdd n j).val` is `j.val` and `(Fin.natAdd n j).val` is `n + j.val`, both by `rfl`,
which is why the inline distinctness proof term in the statement typechecks. -/

private theorem shiFan_cast_ne_nat {n : ℕ} (j k : Fin n) :
    (Fin.castAdd n j : Fin (n + n)) ≠ Fin.natAdd n k := by
  intro h
  have h2 : (j : ℕ) = n + (k : ℕ) := congrArg Fin.val h
  have hj := j.isLt
  omega

private theorem shiFan_cast_inj {n : ℕ} {j k : Fin n}
    (h : (Fin.castAdd n j : Fin (n + n)) = Fin.castAdd n k) : j = k := by
  have h2 : ((Fin.castAdd n j : Fin (n + n)) : ℕ) = ((Fin.castAdd n k : Fin (n + n)) : ℕ) :=
    congrArg Fin.val h
  exact Fin.ext h2

private theorem shiFan_nat_inj {n : ℕ} {j k : Fin n}
    (h : (Fin.natAdd n j : Fin (n + n)) = Fin.natAdd n k) : j = k := by
  have h2 : n + (j : ℕ) = n + (k : ℕ) := congrArg Fin.val h
  exact Fin.ext (by omega)

/-- Control `castAdd n j` (first block), target `natAdd n j` (second block). -/
private def shiFan_gate (n : ℕ) (j : Fin n) : Instr (n + n) :=
  Instr.cnot (Fin.castAdd n j) (Fin.natAdd n j) (shiFan_cast_ne_nat j j)

private theorem shiFan_disj {n : ℕ} {j k : Fin n} (hjk : j ≠ k) :
    Disjoint (shiFan_gate n j).support (shiFan_gate n k).support := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [shiFan_gate, Instr.support, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl
  · rcases hb with h | h
    · exact hjk (shiFan_cast_inj h)
    · exact shiFan_cast_ne_nat j k h
  · rcases hb with h | h
    · exact shiFan_cast_ne_nat k j h.symm
    · exact hjk (shiFan_nat_inj h)

private theorem shiFan_layerOk (n : ℕ) :
    LayerOk ((List.finRange n).map (shiFan_gate n)) := by
  rw [LayerOk, List.pairwise_map]
  exact (List.nodup_finRange n).imp (fun h => shiFan_disj h)

private def shiFan_upd {n : ℕ} (js : List (Fin n)) (x : Bits (n + n)) : Bits (n + n) :=
  Fin.addCases (fun i : Fin n => x (Fin.castAdd n i))
    (fun j : Fin n =>
      if j ∈ js then xor (x (Fin.natAdd n j)) (x (Fin.castAdd n j)) else x (Fin.natAdd n j))

private theorem shiFan_upd_cast {n : ℕ} (js : List (Fin n)) (i : Fin n) (x : Bits (n + n)) :
    shiFan_upd js x (Fin.castAdd n i) = x (Fin.castAdd n i) := by
  simp only [shiFan_upd, Fin.addCases_left, -Fin.natAdd_eq_addNat]

private theorem shiFan_upd_nat {n : ℕ} (js : List (Fin n)) (j : Fin n) (x : Bits (n + n)) :
    shiFan_upd js x (Fin.natAdd n j)
      = if j ∈ js then xor (x (Fin.natAdd n j)) (x (Fin.castAdd n j))
        else x (Fin.natAdd n j) := by
  simp only [shiFan_upd, Fin.addCases_right, -Fin.natAdd_eq_addNat]

private theorem shiFan_upd_nat_notMem {n : ℕ} {js : List (Fin n)} {j : Fin n} (hj : j ∉ js)
    (x : Bits (n + n)) : shiFan_upd js x (Fin.natAdd n j) = x (Fin.natAdd n j) := by
  rw [shiFan_upd_nat js j x, if_neg hj]

private theorem shiFan_upd_nil {n : ℕ} (x : Bits (n + n)) : shiFan_upd [] x = x := by
  funext a
  induction a using Fin.addCases with
  | left i => exact shiFan_upd_cast [] i x
  | right j =>
      have hj : j ∉ ([] : List (Fin n)) := by simp
      exact shiFan_upd_nat_notMem hj x

private theorem shiFan_upd_cons {n : ℕ} (j : Fin n) (rest : List (Fin n)) (hj : j ∉ rest)
    (x : Bits (n + n)) :
    Function.update (shiFan_upd rest x) (Fin.natAdd n j)
        (xor (x (Fin.natAdd n j)) (x (Fin.castAdd n j)))
      = shiFan_upd (j :: rest) x := by
  funext a
  induction a using Fin.addCases with
  | left i =>
      rw [Function.update_of_ne (shiFan_cast_ne_nat i j), shiFan_upd_cast rest i x,
        shiFan_upd_cast (j :: rest) i x]
  | right k =>
      by_cases hk : k = j
      · rw [hk, Function.update_self, shiFan_upd_nat (j :: rest) j x,
          if_pos (show j ∈ j :: rest by simp)]
      · rw [Function.update_of_ne (fun h => hk (shiFan_nat_inj h)),
          shiFan_upd_nat rest k x, shiFan_upd_nat (j :: rest) k x]
        by_cases hkr : k ∈ rest
        · rw [if_pos hkr, if_pos (show k ∈ j :: rest by simp [hkr])]
        · have hkc : k ∉ j :: rest := by
            intro hmem
            rcases List.mem_cons.1 hmem with h1 | h1
            · exact hk h1
            · exact hkr h1
          rw [if_neg hkr, if_neg hkc]

private theorem shiFan_upd_full {n : ℕ} (x : Bits (n + n)) :
    shiFan_upd (List.finRange n) x
      = Fin.addCases (fun i : Fin n => x (Fin.castAdd n i))
          (fun j : Fin n => xor (x (Fin.natAdd n j)) (x (Fin.castAdd n j))) := by
  funext a
  induction a using Fin.addCases with
  | left i =>
      rw [shiFan_upd_cast (List.finRange n) i x, Fin.addCases_left]
      all_goals rfl
  | right j =>
      rw [shiFan_upd_nat (List.finRange n) j x, if_pos (List.mem_finRange j),
        Fin.addCases_right]
      all_goals rfl

private theorem shiFan_runLayer_nil {n : ℕ} (ψ : QState n) : runLayer [] ψ = ψ := by
  simp only [runLayer, List.foldl_nil]

private theorem shiFan_runLayer_cons {n : ℕ} (g : Instr n) (gs : List (Instr n))
    (ψ : QState n) : runLayer (g :: gs) ψ = runLayer gs (g.apply ψ) := by
  simp only [runLayer, List.foldl_cons]

private theorem shiFan_runLayered_single {n : ℕ} (l : List (Instr n)) (φ : QState n) :
    runLayered [l] φ = runLayer l φ := by
  simp only [runLayered, List.foldl_cons, List.foldl_nil]

private theorem shiFan_gate_apply {n : ℕ} (j : Fin n) (φ : QState (n + n))
    (w : Bits (n + n)) :
    (shiFan_gate n j).apply φ w
      = φ (Function.update w (Fin.natAdd n j) (xor (w (Fin.natAdd n j)) (w (Fin.castAdd n j)))) :=
  rfl

private theorem shiFan_fold {n : ℕ} :
    ∀ js : List (Fin n), js.Nodup → ∀ (φ : QState (n + n)) (x : Bits (n + n)),
      runLayer (js.map (shiFan_gate n)) φ x = φ (shiFan_upd js x) := by
  intro js
  induction js with
  | nil =>
      intro _ φ x
      simp only [List.map_nil, shiFan_runLayer_nil, shiFan_upd_nil]
  | cons j rest ih =>
      intro hjs φ x
      have hj : j ∉ rest := (List.nodup_cons.1 hjs).1
      have hrest : rest.Nodup := (List.nodup_cons.1 hjs).2
      rw [List.map_cons, shiFan_runLayer_cons,
        ih hrest ((shiFan_gate n j).apply φ) x,
        shiFan_gate_apply j φ (shiFan_upd rest x),
        shiFan_upd_nat_notMem hj x, shiFan_upd_cast rest j x, shiFan_upd_cons j rest hj x]

private theorem shiE_fan_spec (n : ℕ) :
    (∀ φ : QState (n + n), runLayered [(List.finRange n).map (shiFan_gate n)] φ
        = fun y => φ (Fin.addCases
            (fun i : Fin n => y (Fin.castAdd n i))
            (fun j : Fin n => xor (y (Fin.natAdd n j)) (y (Fin.castAdd n j)))))
      ∧ (∀ l ∈ [(List.finRange n).map (shiFan_gate n)], LayerOk l)
      ∧ depth [(List.finRange n).map (shiFan_gate n)] = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro φ
    funext y
    rw [shiFan_runLayered_single, shiFan_fold (List.finRange n) (List.nodup_finRange n) φ y,
      shiFan_upd_full y]
    all_goals rfl
  · intro l hl
    simp only [List.mem_singleton] at hl
    subst hl
    exact shiFan_layerOk n
  · simp [depth]

/-! ## The public theorem -/

theorem solution {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (w1 w2 w3 s : Fin N) (h12 : w1 ≠ w2) (h13 : w1 ≠ w3) (h23 : w2 ≠ w3)
    (h1s : w1 ≠ s) (h2s : w2 ≠ s) (h3s : w3 ≠ s) (n : ℕ) :
    (∃ tof : Layered N,
        tof =
          [
           [Instr.h r], [Instr.t p], [Instr.t q], [Instr.t r], [Instr.cnot p q hpq], [Instr.t q],
           [Instr.t q], [Instr.t q], [Instr.t q], [Instr.t q], [Instr.t q], [Instr.t q],
           [Instr.cnot p q hpq], [Instr.cnot q r hqr], [Instr.t r], [Instr.t r], [Instr.t r],
           [Instr.t r], [Instr.t r], [Instr.t r], [Instr.t r], [Instr.cnot q r hqr],
           [Instr.cnot p r hpr], [Instr.t r], [Instr.t r], [Instr.t r], [Instr.t r], [Instr.t r],
           [Instr.t r], [Instr.t r], [Instr.cnot p r hpr], [Instr.cnot p r hpr],
           [Instr.cnot q r hqr], [Instr.t r], [Instr.cnot q r hqr], [Instr.cnot p r hpr],
           [Instr.h r]
          ]
        ∧ (∀ ψ : QState N, runLayered tof ψ
            = fun x => ψ (Function.update x r (xor (x r) (x p && x q))))
        ∧ (∀ l ∈ tof, LayerOk l)
        ∧ depth tof = 37)
    ∧ (∃ read : Layered N,
        read =
          [
           [Instr.h s], [Instr.t w1], [Instr.t w2], [Instr.t s], [Instr.cnot w1 w2 h12],
           [Instr.t w2], [Instr.t w2], [Instr.t w2], [Instr.t w2], [Instr.t w2], [Instr.t w2],
           [Instr.t w2], [Instr.cnot w1 w2 h12], [Instr.cnot w2 s h2s], [Instr.t s], [Instr.t s],
           [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.cnot w2 s h2s],
           [Instr.cnot w1 s h1s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s],
           [Instr.t s], [Instr.t s], [Instr.cnot w1 s h1s], [Instr.cnot w1 s h1s],
           [Instr.cnot w2 s h2s], [Instr.t s], [Instr.cnot w2 s h2s], [Instr.cnot w1 s h1s],
           [Instr.h s]
          ] ++
          [
           [Instr.h s], [Instr.t w2], [Instr.t w3], [Instr.t s], [Instr.cnot w2 w3 h23],
           [Instr.t w3], [Instr.t w3], [Instr.t w3], [Instr.t w3], [Instr.t w3], [Instr.t w3],
           [Instr.t w3], [Instr.cnot w2 w3 h23], [Instr.cnot w3 s h3s], [Instr.t s], [Instr.t s],
           [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.cnot w3 s h3s],
           [Instr.cnot w2 s h2s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s],
           [Instr.t s], [Instr.t s], [Instr.cnot w2 s h2s], [Instr.cnot w2 s h2s],
           [Instr.cnot w3 s h3s], [Instr.t s], [Instr.cnot w3 s h3s], [Instr.cnot w2 s h2s],
           [Instr.h s]
          ] ++
          [
           [Instr.h s], [Instr.t w1], [Instr.t w3], [Instr.t s], [Instr.cnot w1 w3 h13],
           [Instr.t w3], [Instr.t w3], [Instr.t w3], [Instr.t w3], [Instr.t w3], [Instr.t w3],
           [Instr.t w3], [Instr.cnot w1 w3 h13], [Instr.cnot w3 s h3s], [Instr.t s], [Instr.t s],
           [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.cnot w3 s h3s],
           [Instr.cnot w1 s h1s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s], [Instr.t s],
           [Instr.t s], [Instr.t s], [Instr.cnot w1 s h1s], [Instr.cnot w1 s h1s],
           [Instr.cnot w3 s h3s], [Instr.t s], [Instr.cnot w3 s h3s], [Instr.cnot w1 s h1s],
           [Instr.h s]
          ]
        ∧ (∀ ψ : QState N, runLayered read ψ
            = fun x => ψ (Function.update x s
                (xor (x s) (xor (xor (x w1 && x w2) (x w2 && x w3)) (x w1 && x w3)))))
        ∧ (∀ l ∈ read, LayerOk l)
        ∧ depth read = 111)
    ∧ (∃ fan : Layered (n + n),
        fan =
          [(List.finRange n).map (fun j : Fin n =>
            Instr.cnot (Fin.castAdd n j) (Fin.natAdd n j)
              (fun hEq => absurd (congrArg Fin.val hEq)
                (Nat.ne_of_lt (Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right n (j : ℕ))))))]
        ∧ (∀ φ : QState (n + n), runLayered fan φ
            = fun y => φ (Fin.addCases
                (fun i : Fin n => y (Fin.castAdd n i))
                (fun j : Fin n => xor (y (Fin.natAdd n j)) (y (Fin.castAdd n j)))))
        ∧ (∀ l ∈ fan, LayerOk l)
        ∧ depth fan = 1)
    ∧ (∃ c3 : Layered 3,
        c3 =
          [
           [Instr.h 2], [Instr.t (0 : Fin 3)], [Instr.t 1], [Instr.t 2],
           [Instr.cnot (0 : Fin 3) 1 (by decide)], [Instr.t 1], [Instr.t 1], [Instr.t 1],
           [Instr.t 1], [Instr.t 1], [Instr.t 1], [Instr.t 1],
           [Instr.cnot (0 : Fin 3) 1 (by decide)], [Instr.cnot 1 2 (by decide)], [Instr.t 2],
           [Instr.t 2], [Instr.t 2], [Instr.t 2], [Instr.t 2], [Instr.t 2], [Instr.t 2],
           [Instr.cnot 1 2 (by decide)], [Instr.cnot (0 : Fin 3) 2 (by decide)], [Instr.t 2],
           [Instr.t 2], [Instr.t 2], [Instr.t 2], [Instr.t 2], [Instr.t 2], [Instr.t 2],
           [Instr.cnot (0 : Fin 3) 2 (by decide)], [Instr.cnot (0 : Fin 3) 2 (by decide)],
           [Instr.cnot 1 2 (by decide)], [Instr.t 2], [Instr.cnot 1 2 (by decide)],
           [Instr.cnot (0 : Fin 3) 2 (by decide)], [Instr.h 2]
          ]
        ∧ ∀ ψ : QState 3,
            runLayered c3 ψ ![true, true, false] = ψ ![true, true, true]
            ∧ runLayered c3 ψ ![true, true, true] = ψ ![true, true, false]
            ∧ runLayered c3 ψ ![true, false, false] = ψ ![true, false, false]
            ∧ runLayered c3 ψ ![false, true, true] = ψ ![false, true, true]) := by
  obtain ⟨htA, htB, htC⟩ := shiE_tof_spec p q r hpq hpr hqr
  obtain ⟨hrA, hrB, hrC⟩ := shiE_read_spec w1 w2 w3 s h12 h13 h23 h1s h2s h3s
  obtain ⟨hfA, hfB, hfC⟩ := shiE_fan_spec n
  obtain ⟨h3A, -, -⟩ := shiE_tof_spec (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
  refine ⟨⟨(shiTof_gates p q r hpq hpr hqr).map (fun g => [g]), ?_, htA, htB, htC⟩,
    ⟨shiE_R w1 w2 w3 s h12 h13 h23 h1s h2s h3s, ?_, hrA, hrB, hrC⟩,
    ⟨[(List.finRange n).map (shiFan_gate n)], ?_, hfA, hfB, hfC⟩,
    ⟨(shiTof_gates (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)).map (fun g => [g]),
      ?_, ?_⟩⟩
  · first
      | rfl
      | simp only [shiTof_gates, List.map_cons, List.map_nil]
  · first
      | rfl
      | simp only [shiE_R, shiE_T, shiTof_gates, List.map_cons, List.map_nil]
  · first
      | rfl
      | simp only [shiFan_gate]
  · first
      | rfl
      | simp only [shiTof_gates, List.map_cons, List.map_nil]
  · intro ψ
    have hact := h3A ψ
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals
      first
        | exact (congrFun hact _).trans (congrArg ψ (by decide))
        | exact (congrFun hact _).trans (congrArg ψ (by funext i; fin_cases i <;> rfl))
        | exact (congrFun hact _).trans (congrArg ψ (by funext i; fin_cases i <;> simp))
        | (rw [hact]; exact congrArg ψ (by decide))

