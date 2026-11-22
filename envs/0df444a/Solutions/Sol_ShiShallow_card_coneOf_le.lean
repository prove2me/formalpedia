-- Prove2me | solution 1 for ShiShallow.card_coneOf_le
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T03:05:40.337582+00:00
-- url     : https://prove2.me/submissions/7389568c-33ef-4948-b211-25d03433c255

import Definitions.Def_ShiShallow_Core

namespace ShiShallow



/-! ## Proved structural facts -/

/-- `coneStep` tests each gate against the **incoming** set, not against the accumulator.
That is deliberate: within a layer whose supports are pairwise disjoint no cascading can
occur, and testing against the accumulator would over-approximate the cone. -/
theorem coneStep_cons {n : ℕ} (g : Instr n) (t : List (Instr n)) (S : Finset (Fin n)) :
    coneStep (g :: t) S =
      if (g.support ∩ S).Nonempty then g.support ∪ coneStep t S else coneStep t S := rfl

theorem coneStep_nil {n : ℕ} (S : Finset (Fin n)) : coneStep [] S = S := rfl

theorem coneOf_cons {n : ℕ} (l : List (Instr n)) (t : Layered n) (S : Finset (Fin n)) :
    coneOf (l :: t) S = coneStep l (coneOf t S) := rfl

theorem subset_coneStep {n : ℕ} (l : List (Instr n)) (S : Finset (Fin n)) :
    S ⊆ coneStep l S := by
  induction l with
  | nil => exact fun a ha => ha
  | cons g t ih =>
      rw [coneStep_cons]
      split
      · exact fun a ha => Finset.mem_union_right _ (ih ha)
      · exact ih

theorem subset_coneOf {n : ℕ} (c : Layered n) (S : Finset (Fin n)) : S ⊆ coneOf c S := by
  induction c with
  | nil => exact fun a ha => ha
  | cons l t ih =>
      rw [coneOf_cons]
      exact fun a ha => subset_coneStep l (coneOf t S) (ih ha)

theorem depth_nil {n : ℕ} : depth ([] : Layered n) = 0 := rfl

theorem coneOf_nil {n : ℕ} (S : Finset (Fin n)) : coneOf ([] : Layered n) S = S := rfl


/-! ## Support facts -/

theorem support_nonempty {n : ℕ} (g : Instr n) : g.support.Nonempty := by
  cases g with
  | h i => exact ⟨i, by simp [Instr.support]⟩
  | s i => exact ⟨i, by simp [Instr.support]⟩
  | t i => exact ⟨i, by simp [Instr.support]⟩
  | x i => exact ⟨i, by simp [Instr.support]⟩
  | cnot i j _ => exact ⟨i, by simp [Instr.support]⟩

theorem card_support_le_two {n : ℕ} (g : Instr n) : g.support.card ≤ 2 := by
  cases g with
  | h i => simp [Instr.support]
  | s i => simp [Instr.support]
  | t i => simp [Instr.support]
  | x i => simp [Instr.support]
  | cnot i j _ =>
      simp only [Instr.support]
      exact (Finset.card_insert_le _ _).trans (by simp)

/-- A gate meeting `S` contributes at most one wire outside `S`: its support has at most two
wires and at least one of them already lies in `S`. -/
theorem card_sdiff_support_le_one {n : ℕ} (g : Instr n) (S : Finset (Fin n))
    (h : (g.support ∩ S).Nonempty) : (g.support \ S).card ≤ 1 := by
  obtain ⟨a, ha⟩ := h
  rw [Finset.mem_inter] at ha
  have hsub : g.support \ S ⊆ g.support.erase a := by
    intro b hb
    rw [Finset.mem_sdiff] at hb
    refine Finset.mem_erase.mpr ⟨?_, hb.1⟩
    intro hba
    exact hb.2 (hba ▸ ha.2)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem ha.1] at hcard
  have h2 := card_support_le_two g
  omega

/-! ## (a) the cone grows by at most one wire per meeting gate -/

theorem card_sdiff_coneStep_le {n : ℕ} (l : List (Instr n)) (S : Finset (Fin n)) :
    ((coneStep l S) \ S).card
      ≤ (l.filter (fun g => decide (g.support ∩ S).Nonempty)).length := by
  induction l with
  | nil => simp [coneStep_nil]
  | cons g t ih =>
      rw [coneStep_cons]
      by_cases h : (g.support ∩ S).Nonempty
      · rw [if_pos h, List.filter_cons_of_pos (by simpa using h), List.length_cons]
        have hsub : (g.support ∪ coneStep t S) \ S
            ⊆ (g.support \ S) ∪ (coneStep t S \ S) := by
          intro a ha
          rw [Finset.mem_sdiff, Finset.mem_union] at ha
          rcases ha.1 with h1 | h2
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h1, ha.2⟩)
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h2, ha.2⟩)
        have h1 := card_sdiff_support_le_one g S h
        calc ((g.support ∪ coneStep t S) \ S).card
            ≤ ((g.support \ S) ∪ (coneStep t S \ S)).card := Finset.card_le_card hsub
          _ ≤ (g.support \ S).card + (coneStep t S \ S).card := Finset.card_union_le _ _
          _ ≤ 1 + (t.filter (fun g => decide (g.support ∩ S).Nonempty)).length := by
              have := ih; omega
          _ = (t.filter (fun g => decide (g.support ∩ S).Nonempty)).length + 1 := by omega
      · rw [if_neg h, List.filter_cons_of_neg (by simpa using h)]
        exact ih

/-! ## Mission targets -/


/-! ## (b) a well-formed layer has at most `|S|` gates meeting `S` -/

theorem length_filter_meets_le {n : ℕ} (l : List (Instr n)) (hl : LayerOk l) :
    ∀ S : Finset (Fin n),
      (l.filter (fun g => decide (g.support ∩ S).Nonempty)).length ≤ S.card := by
  induction l with
  | nil => intro S; simp
  | cons g t ih =>
      intro S
      rw [LayerOk, List.pairwise_cons] at hl
      obtain ⟨hdisj, ht⟩ := hl
      by_cases h : (g.support ∩ S).Nonempty
      · rw [List.filter_cons_of_pos (by simpa using h), List.length_cons]
        have hfe : t.filter (fun b => decide (b.support ∩ S).Nonempty)
            = t.filter (fun b => decide (b.support ∩ (S \ g.support)).Nonempty) := by
          refine List.filter_congr ?_
          intro b hb
          have hd : Disjoint b.support g.support := (hdisj b hb).symm
          simp only [decide_eq_decide]
          constructor
          · rintro ⟨a, ha⟩
            rw [Finset.mem_inter] at ha
            refine ⟨a, Finset.mem_inter.mpr ⟨ha.1, Finset.mem_sdiff.mpr ⟨ha.2, ?_⟩⟩⟩
            exact fun hg => Finset.disjoint_left.mp hd ha.1 hg
          · rintro ⟨a, ha⟩
            rw [Finset.mem_inter, Finset.mem_sdiff] at ha
            exact ⟨a, Finset.mem_inter.mpr ⟨ha.1, ha.2.1⟩⟩
        rw [hfe]
        obtain ⟨a, ha⟩ := h
        rw [Finset.mem_inter] at ha
        have hlt : (S \ g.support).card < S.card := by
          refine Finset.card_lt_card ⟨Finset.sdiff_subset, ?_⟩
          intro hsub
          exact (Finset.mem_sdiff.mp (hsub ha.2)).2 ha.1
        have h1 := ih ht (S \ g.support)
        omega
      · rw [List.filter_cons_of_neg (by simpa using h)]
        exact ih ht S

/-- MILESTONE: one well-formed layer at most doubles the cone. -/
theorem card_coneStep_le {n : ℕ} (l : List (Instr n)) (hl : LayerOk l) (S : Finset (Fin n)) :
    (coneStep l S).card ≤ 2 * S.card := by
  have hsub : S ⊆ coneStep l S := subset_coneStep l S
  have hle : S.card ≤ (coneStep l S).card := Finset.card_le_card hsub
  have hint : S ∩ coneStep l S = S := Finset.inter_eq_left.mpr hsub
  have hsd : ((coneStep l S) \ S).card = (coneStep l S).card - S.card := by
    rw [Finset.card_sdiff, hint]
  have ha := card_sdiff_coneStep_le l S
  have hb := length_filter_meets_le l hl S
  omega

/-- MILESTONE / GOAL (combinatorial half): the cone of a depth-`d` circuit is at most `2^d`
times larger. -/
theorem card_coneOf_le {n : ℕ} (c : Layered n) (hc : ∀ l ∈ c, LayerOk l) (S : Finset (Fin n)) :
    (coneOf c S).card ≤ 2 ^ depth c * S.card := by
  induction c with
  | nil => simp [depth, coneOf_nil]
  | cons l t ih =>
      have hl : LayerOk l := hc l List.mem_cons_self
      have ht : ∀ l' ∈ t, LayerOk l' := fun l' h => hc l' (List.mem_cons_of_mem _ h)
      rw [coneOf_cons]
      calc (coneStep l (coneOf t S)).card
          ≤ 2 * (coneOf t S).card := card_coneStep_le l hl _
        _ ≤ 2 * (2 ^ depth t * S.card) := by
            have := ih ht; omega
        _ = 2 ^ depth (l :: t) * S.card := by
            simp [depth, pow_succ]; ring


/-- COROLLARY: if every input wire lies in the **syntactic** causal cone of `out`, then
`n ≤ 2 ^ depth`. Two honest caveats. The hypothesis is cone membership, not genuine
functional dependence — bridging the two is exactly `acceptProb_eq_of_agree_on_cone`. And
`depth` is the outer list length, so padding with empty layers (which are vacuously
`LayerOk`) inflates the bound. The conclusion also discards any ancilla wires that lie in
the cone, so it is weaker than the available `(coneOf c {out}).card ≤ 2 ^ depth c`. -/
theorem card_le_two_pow_depth_of_all_relevant {n m : ℕ} (c : Layered (n + m))
    (out : Fin (n + m)) (hc : ∀ l ∈ c, LayerOk l)
    (hall : ∀ i : Fin n, Fin.castAdd m i ∈ coneOf c {out}) :
    n ≤ 2 ^ depth c := by
  -- the cone of a single wire has at most `2 ^ depth` wires
  have h2 := card_coneOf_le c hc ({out} : Finset (Fin (n + m)))
  rw [Finset.card_singleton, mul_one] at h2
  -- and it contains the images of all `n` input wires, which are distinct
  have hle : (Finset.univ : Finset (Fin n)).card ≤ (coneOf c {out}).card :=
    Finset.card_le_card_of_injOn (fun i => Fin.castAdd m i)
      (fun i _ => hall i)
      (fun a _ b _ hab => by simpa [Fin.ext_iff] using hab)
  rw [Finset.card_univ, Fintype.card_fin] at hle
  omega


/-- CNOT permutes the computational basis, and is an involution when `i ≠ j`. -/
def cnotEquiv {n : ℕ} (i j : Fin n) (hij : i ≠ j) : Bits n ≃ Bits n where
  toFun x := Function.update x j (xor (x j) (x i))
  invFun x := Function.update x j (xor (x j) (x i))
  left_inv x := by
    funext k
    by_cases hk : k = j
    · rw [hk]
      simp only [Function.update_self, Function.update_of_ne hij]
      cases hxj : x j <;> cases hxi : x i <;> simp
    · simp [Function.update_of_ne hk]
  right_inv x := by
    funext k
    by_cases hk : k = j
    · rw [hk]
      simp only [Function.update_self, Function.update_of_ne hij]
      cases hxj : x j <;> cases hxi : x i <;> simp
    · simp [Function.update_of_ne hk]

/-- CNOT preserves the sum of squared amplitudes: it merely permutes basis strings. -/
theorem sum_norm_sq_cnotState {n : ℕ} (i j : Fin n) (hij : i ≠ j) (ψ : QState n) :
    ∑ x : Bits n, ‖cnotState i j hij ψ x‖ ^ 2 = ∑ x : Bits n, ‖ψ x‖ ^ 2 :=
  Fintype.sum_equiv (cnotEquiv i j hij) _ _ (fun _ => rfl)


/-- The complex form of unitary norm preservation on a two-element index: for `U` unitary,
`∑ₐ conj((Uv)ₐ)·(Uv)ₐ = ∑_b conj(v b)·v b`. The four entries of `Uᴴ U = 1` are exactly the
coefficients needed. -/
theorem sum_conj_mul_mulVec {U : Matrix Bool Bool ℂ} (hU : U.conjTranspose * U = 1)
    (v : Bool → ℂ) :
    ∑ a : Bool, (starRingEnd ℂ) (∑ b : Bool, U a b * v b) * (∑ b : Bool, U a b * v b)
      = ∑ b : Bool, (starRingEnd ℂ) (v b) * v b := by
  have e00 := congrFun (congrFun hU false) false
  have e01 := congrFun (congrFun hU false) true
  have e10 := congrFun (congrFun hU true) false
  have e11 := congrFun (congrFun hU true) true
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
             Fintype.sum_bool] at e00 e01 e10 e11
  norm_num at e00 e01 e10 e11
  -- `norm_num` leaves the hypotheses in `starRingEnd` form; keep the goal in the same
  -- form so `ring` sees one atom per conjugated entry rather than `star` and
  -- `starRingEnd` as unrelated symbols.
  simp only [Fintype.sum_bool, map_add, map_mul]
  linear_combination ((starRingEnd ℂ) (v false) * v false) * e00
    + ((starRingEnd ℂ) (v false) * v true) * e01
    + ((starRingEnd ℂ) (v true) * v false) * e10
    + ((starRingEnd ℂ) (v true) * v true) * e11


/-- Unitary norm preservation on a two-element index, in terms of `‖·‖²`. -/
theorem sum_norm_sq_mulVec {U : Matrix Bool Bool ℂ} (hU : U.conjTranspose * U = 1)
    (v : Bool → ℂ) :
    ∑ a : Bool, ‖∑ b : Bool, U a b * v b‖ ^ 2 = ∑ b : Bool, ‖v b‖ ^ 2 := by
  have h := sum_conj_mul_mulVec hU v
  have hz : ∀ z : ℂ, (starRingEnd ℂ) z * z = (Complex.normSq z : ℂ) := by
    intro z; rw [mul_comm]; exact Complex.mul_conj z
  simp only [hz] at h
  simp only [Complex.sq_norm]
  exact_mod_cast h


/-! ### Lifting the two-element result to a wire, via the fibre decomposition -/

theorem funSplitAt_symm_at_i {n : ℕ} (i : Fin n) (a : Bool)
    (r : {j : Fin n // j ≠ i} → Bool) :
    (Equiv.funSplitAt i Bool).symm (a, r) i = a := by
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

theorem update_funSplitAt_symm {n : ℕ} (i : Fin n) (a b : Bool)
    (r : {j : Fin n // j ≠ i} → Bool) :
    Function.update ((Equiv.funSplitAt i Bool).symm (a, r)) i b
      = (Equiv.funSplitAt i Bool).symm (b, r) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [Function.update_of_ne hj, Equiv.funSplitAt, Equiv.piSplitAt, dif_neg hj]

/-- On the fibre over `r`, applying a one-qubit gate at wire `i` is exactly multiplication
by the `2 × 2` matrix. -/
theorem apply1_at_fibre {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n) (ψ : QState n)
    (a : Bool) (r : {j : Fin n // j ≠ i} → Bool) :
    apply1 U i ψ ((Equiv.funSplitAt i Bool).symm (a, r))
      = ∑ b : Bool, U a b * ψ ((Equiv.funSplitAt i Bool).symm (b, r)) := by
  unfold apply1
  rw [funSplitAt_symm_at_i]
  exact Finset.sum_congr rfl (fun b _ => by rw [update_funSplitAt_symm])

/-- A unitary one-qubit gate preserves the sum of squared amplitudes. -/
theorem sum_norm_sq_apply1 {n : ℕ} {U : Matrix Bool Bool ℂ}
    (hU : U.conjTranspose * U = 1) (i : Fin n) (ψ : QState n) :
    ∑ x : Bits n, ‖apply1 U i ψ x‖ ^ 2 = ∑ x : Bits n, ‖ψ x‖ ^ 2 := by
  classical
  set e := Equiv.funSplitAt i Bool with he
  have hL : ∑ x : Bits n, ‖apply1 U i ψ x‖ ^ 2
      = ∑ p : Bool × ({j : Fin n // j ≠ i} → Bool), ‖apply1 U i ψ (e.symm p)‖ ^ 2 :=
    Fintype.sum_equiv e _ _ (fun x => by simp)
  have hR : ∑ x : Bits n, ‖ψ x‖ ^ 2
      = ∑ p : Bool × ({j : Fin n // j ≠ i} → Bool), ‖ψ (e.symm p)‖ ^ 2 :=
    Fintype.sum_equiv e _ _ (fun x => by simp)
  rw [hL, hR, Fintype.sum_prod_type, Fintype.sum_prod_type,
      Finset.sum_comm (s := (Finset.univ : Finset Bool)), 
      Finset.sum_comm (s := (Finset.univ : Finset Bool))]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  simp only [he, apply1_at_fibre]
  exact sum_norm_sq_mulVec hU (fun b => ψ ((Equiv.funSplitAt i Bool).symm (b, r)))


/-! ## Unitarity and normalisation (flagged by audit as asserted nowhere) -/

theorem inv_sqrt_two_mul_self : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [one_div]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, hr]
  push_cast
  ring

theorem hMat_unitary : hMat.conjTranspose * hMat = 1 := by
  ext a c
  cases a <;> cases c <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hMat, Matrix.one_apply,
          Fintype.sum_bool, inv_sqrt_two_mul_self] <;>
    ring_nf <;> linear_combination inv_sqrt_two_mul_self

theorem sMat_unitary : sMat.conjTranspose * sMat = 1 := by
  ext a c
  cases a <;> cases c <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, sMat, Matrix.one_apply,
          Fintype.sum_bool, Complex.conj_I] <;> ring_nf <;> simp [Complex.I_mul_I]

theorem xMat_unitary : xMat.conjTranspose * xMat = 1 := by
  ext a c
  cases a <;> cases c <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, xMat, Matrix.one_apply,
          Fintype.sum_bool]

theorem tMat_unitary : tMat.conjTranspose * tMat = 1 := by
  have key : (starRingEnd ℂ) (Complex.exp (Complex.I * Real.pi / 4))
      * Complex.exp (Complex.I * Real.pi / 4) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    have : (starRingEnd ℂ) (Complex.I * Real.pi / 4) + Complex.I * Real.pi / 4 = 0 := by
      simp [map_div₀, map_mul, Complex.conj_I, map_ofNat]
      ring
    rw [this, Complex.exp_zero]
  ext a c
  cases a <;> cases c <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, tMat, Matrix.one_apply,
          Fintype.sum_bool, key]

/-! ### Norm preservation for whole circuits -/

theorem Instr.apply_norm {n : ℕ} (g : Instr n) (ψ : QState n) :
    ∑ x : Bits n, ‖g.apply ψ x‖ ^ 2 = ∑ x : Bits n, ‖ψ x‖ ^ 2 := by
  cases g with
  | h i => exact sum_norm_sq_apply1 hMat_unitary i ψ
  | s i => exact sum_norm_sq_apply1 sMat_unitary i ψ
  | t i => exact sum_norm_sq_apply1 tMat_unitary i ψ
  | x i => exact sum_norm_sq_apply1 xMat_unitary i ψ
  | cnot i j hij => exact sum_norm_sq_cnotState i j hij ψ

theorem runLayer_norm {n : ℕ} (l : List (Instr n)) (ψ : QState n) :
    ∑ x : Bits n, ‖runLayer l ψ x‖ ^ 2 = ∑ x : Bits n, ‖ψ x‖ ^ 2 := by
  induction l generalizing ψ with
  | nil => rfl
  | cons g t ih => exact (ih (g.apply ψ)).trans (Instr.apply_norm g ψ)

/-- The input state `|x⟩ ⊗ |0…0⟩` is a unit vector. -/
theorem inputState_norm {n m : ℕ} (x : Bits n) :
    ∑ y : Bits (n + m), ‖inputState (m := m) x y‖ ^ 2 = 1 := by
  classical
  set y₀ : Bits (n + m) := fun k => Fin.addCases (fun i => x i) (fun _ => false) k with hy₀
  have hP : ∀ y : Bits (n + m),
      ((∀ i : Fin n, y (Fin.castAdd m i) = x i) ∧ (∀ k : Fin m, y (Fin.natAdd n k) = false))
      ↔ y = y₀ := by
    intro y
    constructor
    · rintro ⟨h1, h2⟩
      funext k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · simpa [hy₀] using h1 i
      · simpa [hy₀] using h2 j
    · rintro rfl
      exact ⟨fun i => by simp [hy₀], fun j => by simp [hy₀]⟩
  have hval : ∀ y : Bits (n + m), ‖inputState (m := m) x y‖ ^ 2 = if y = y₀ then 1 else 0 := by
    intro y
    unfold inputState
    by_cases hy : y = y₀
    · rw [if_pos ((hP y).mpr hy), if_pos hy]; simp
    · rw [if_neg (fun hc => hy ((hP y).mp hc)), if_neg hy]; simp
  simp [hval]

/-- Circuit evolution preserves the `ℓ²` norm; without this nothing pins `acceptProb` to a
probability. -/
theorem runLayered_norm {n : ℕ} (c : Layered n) (ψ : QState n) :
    ∑ x : Bits n, ‖runLayered c ψ x‖ ^ 2 = ∑ x : Bits n, ‖ψ x‖ ^ 2 := by
  induction c generalizing ψ with
  | nil => rfl
  | cons l t ih => exact (ih (runLayer l ψ)).trans (runLayer_norm l ψ)

theorem acceptProb_nonneg {n m : ℕ} (c : Layered (n + m)) (x : Bits n) (out : Fin (n + m)) :
    0 ≤ acceptProb c x out := by
  refine Finset.sum_nonneg fun y _ => ?_
  split
  · positivity
  · exact le_refl 0

theorem acceptProb_le_one {n m : ℕ} (c : Layered (n + m)) (x : Bits n) (out : Fin (n + m)) :
    acceptProb c x out ≤ 1 := by
  unfold acceptProb
  calc ∑ y : Bits (n + m), (if y out then ‖runLayered c (inputState x) y‖ ^ 2 else 0)
      ≤ ∑ y : Bits (n + m), ‖runLayered c (inputState x) y‖ ^ 2 := by
        refine Finset.sum_le_sum (fun y _ => ?_)
        split
        · exact le_refl _
        · positivity
    _ = ∑ y : Bits (n + m), ‖inputState (m := m) x y‖ ^ 2 := runLayered_norm _ _
    _ = 1 := inputState_norm x

/-! ## Composition of circuits, and the output distribution

Two things are recorded here. First, that depth, dynamics and causal cones all compose in the
expected way under concatenation of circuits — the cone of a composite is the cone of the
first part applied to the cone of the second, which is the structural fact behind every
light-cone argument. Second, that a circuit's output is a genuine probability distribution
over basis strings, so that `acceptProb` is the mass of the event "the output wire reads 1". -/

theorem runLayer_append {n : ℕ} (l₁ l₂ : List (Instr n)) (ψ : QState n) :
    runLayer (l₁ ++ l₂) ψ = runLayer l₂ (runLayer l₁ ψ) := by
  unfold runLayer
  rw [List.foldl_append]

theorem runLayered_append {n : ℕ} (c₁ c₂ : Layered n) (ψ : QState n) :
    runLayered (c₁ ++ c₂) ψ = runLayered c₂ (runLayered c₁ ψ) := by
  unfold runLayered
  rw [List.foldl_append]

theorem depth_append {n : ℕ} (c₁ c₂ : Layered n) :
    depth (c₁ ++ c₂) = depth c₁ + depth c₂ := by
  simp [depth]

/-- Causal cones compose contravariantly: propagating back through `c₁ ++ c₂` is propagating
back through `c₂` and then through `c₁`. -/
theorem coneOf_append {n : ℕ} (c₁ c₂ : Layered n) (S : Finset (Fin n)) :
    coneOf (c₁ ++ c₂) S = coneOf c₁ (coneOf c₂ S) := by
  unfold coneOf
  rw [List.foldr_append]

theorem coneStep_mono {n : ℕ} (l : List (Instr n)) {S T : Finset (Fin n)} (h : S ⊆ T) :
    coneStep l S ⊆ coneStep l T := by
  classical
  induction l with
  | nil => simpa [coneStep_nil] using h
  | cons g t ih =>
      rw [coneStep_cons, coneStep_cons]
      by_cases hS : (g.support ∩ S).Nonempty
      · obtain ⟨a, ha⟩ := hS
        have ha' := Finset.mem_inter.1 ha
        have hT : (g.support ∩ T).Nonempty :=
          ⟨a, Finset.mem_inter.2 ⟨ha'.1, h ha'.2⟩⟩
        rw [if_pos ⟨a, ha⟩, if_pos hT]
        exact Finset.union_subset_union (Finset.Subset.refl _) ih
      · rw [if_neg hS]
        by_cases hT : (g.support ∩ T).Nonempty
        · rw [if_pos hT]
          exact ih.trans Finset.subset_union_right
        · rw [if_neg hT]
          exact ih

theorem coneOf_mono {n : ℕ} (c : Layered n) {S T : Finset (Fin n)} (h : S ⊆ T) :
    coneOf c S ⊆ coneOf c T := by
  induction c with
  | nil => simpa [coneOf_nil] using h
  | cons l t ih =>
      rw [coneOf_cons, coneOf_cons]
      exact coneStep_mono l ih


theorem outDist_nonneg {n m : ℕ} (c : Layered (n + m)) (x : Bits n) (y : Bits (n + m)) :
    0 ≤ outDist c x y := by
  unfold outDist
  positivity

/-- The output of any circuit is a probability distribution. -/
theorem sum_outDist_eq_one {n m : ℕ} (c : Layered (n + m)) (x : Bits n) :
    ∑ y : Bits (n + m), outDist c x y = 1 := by
  unfold outDist
  rw [runLayered_norm]
  exact inputState_norm x

theorem outDist_le_one {n m : ℕ} (c : Layered (n + m)) (x : Bits n) (y : Bits (n + m)) :
    outDist c x y ≤ 1 := by
  classical
  calc outDist c x y
      ≤ ∑ y' : Bits (n + m), outDist c x y' :=
        Finset.single_le_sum (fun y' _ => outDist_nonneg c x y') (Finset.mem_univ y)
    _ = 1 := sum_outDist_eq_one c x

/-- `acceptProb` is the mass this distribution puts on the strings whose output wire reads 1. -/
theorem acceptProb_eq_sum_outDist {n m : ℕ} (c : Layered (n + m)) (x : Bits n)
    (out : Fin (n + m)) :
    acceptProb c x out = ∑ y : Bits (n + m), if y out then outDist c x y else 0 := rfl

/-! ## Sharpness of the light-cone bound

`card_coneOf_le` bounds a cone by `2 ^ depth`; on its own that leaves open whether the
exponent is an artefact of the proof. The circuit built here — a CNOT binary tree that
doubles the cone at every layer — attains the bound exactly, so the factor is correct and
cannot be improved. -/

/-- The wires whose index is below `k`. -/
def initSeg {n : ℕ} (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a => (a : ℕ) < k)

theorem mem_initSeg {n k : ℕ} (a : Fin n) : a ∈ initSeg k ↔ (a : ℕ) < k := by
  simp [initSeg]

theorem card_initSeg {n k : ℕ} (hk : k ≤ n) : (initSeg (n := n) k).card = k := by
  classical
  have himg : initSeg (n := n) k = Finset.image (Fin.castLE hk) Finset.univ := by
    ext a
    simp only [mem_initSeg, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro ha
      exact ⟨⟨(a : ℕ), ha⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      simpa using b.2
  rw [himg, Finset.card_image_of_injective _ (Fin.castLE_injective hk), Finset.card_univ,
    Fintype.card_fin]

/-! ### Two general facts about `coneStep` -/

/-- When every gate of a layer meets `S`, the cone step is just the union of all the supports. -/
theorem coneStep_of_all_meet {n : ℕ} (l : List (Instr n)) (S : Finset (Fin n))
    (hmeet : ∀ g ∈ l, (g.support ∩ S).Nonempty) :
    coneStep l S = l.foldr (fun g acc => g.support ∪ acc) S := by
  induction l with
  | nil => rfl
  | cons g t ih =>
      rw [coneStep_cons, if_pos (hmeet g (by simp)), List.foldr_cons,
        ih (fun g' hg' => hmeet g' (by simp [hg']))]

theorem mem_foldr_union {n : ℕ} (l : List (Instr n)) (S : Finset (Fin n)) (a : Fin n) :
    a ∈ l.foldr (fun g acc => g.support ∪ acc) S ↔ a ∈ S ∨ ∃ g ∈ l, a ∈ g.support := by
  induction l with
  | nil => simp
  | cons g t ih =>
      simp only [List.foldr_cons, Finset.mem_union, ih, List.mem_cons, exists_eq_or_imp]
      tauto

/-! ### The doubling layer -/

/-- The gates of one doubling layer, for control wires `0, …, k-1`: each wire `i` below
`2 ^ t` is CNOT'd onto the wire `2 ^ t + i`. -/
def treeGates {n : ℕ} (t : ℕ) (h : 2 ^ t + 2 ^ t ≤ n) : ℕ → List (Instr n)
  | 0 => []
  | (k + 1) =>
      if hk : k < 2 ^ t then
        Instr.cnot ⟨k, by omega⟩ ⟨2 ^ t + k, by omega⟩
            (by
              simp only [ne_eq, Fin.mk.injEq]
              have hp : 0 < 2 ^ t := by positivity
              omega)
          :: treeGates t h k
      else treeGates t h k

/-- Every gate of `treeGates` is the CNOT pair `{i, 2 ^ t + i}` for some `i < k`. -/
theorem treeGates_support {n t : ℕ} (h : 2 ^ t + 2 ^ t ≤ n) :
    ∀ (k : ℕ), ∀ g ∈ treeGates t h k, ∃ i, i < k ∧ i < 2 ^ t ∧
      ∀ a : Fin n, a ∈ g.support ↔ ((a : ℕ) = i ∨ (a : ℕ) = 2 ^ t + i) := by
  intro k
  induction k with
  | zero => intro g hg; simp [treeGates] at hg
  | succ k ih =>
      intro g hg
      rw [treeGates] at hg
      split_ifs at hg with hk
      · rcases List.mem_cons.1 hg with rfl | hg'
        · refine ⟨k, by omega, hk, fun a => ?_⟩
          simp [Instr.support, Fin.ext_iff]
        · obtain ⟨i, hi1, hi2, hi3⟩ := ih g hg'
          exact ⟨i, by omega, hi2, hi3⟩
      · obtain ⟨i, hi1, hi2, hi3⟩ := ih g hg
        exact ⟨i, by omega, hi2, hi3⟩

/-- Conversely, every wire of every pair `{i, 2 ^ t + i}` with `i < k` is covered. -/
theorem exists_mem_treeGates {n t : ℕ} (h : 2 ^ t + 2 ^ t ≤ n) :
    ∀ (k : ℕ), k ≤ 2 ^ t → ∀ (i : ℕ), i < k → ∀ a : Fin n,
      ((a : ℕ) = i ∨ (a : ℕ) = 2 ^ t + i) → ∃ g ∈ treeGates t h k, a ∈ g.support := by
  intro k
  induction k with
  | zero => intro _ i hi; omega
  | succ k ih =>
      intro hk i hi a ha
      have hklt : k < 2 ^ t := by omega
      rw [treeGates, dif_pos hklt]
      by_cases hik : i = k
      · subst hik
        refine ⟨_, List.mem_cons_self .., ?_⟩
        simp only [Instr.support, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
        exact ha
      · obtain ⟨g, hg, hga⟩ := ih (by omega) i (by omega) a ha
        exact ⟨g, List.mem_cons_of_mem _ hg, hga⟩

theorem layerOk_treeGates {n t : ℕ} (h : 2 ^ t + 2 ^ t ≤ n) :
    ∀ (k : ℕ), LayerOk (treeGates t h k) := by
  intro k
  induction k with
  | zero => simp [treeGates, LayerOk]
  | succ k ih =>
      rw [treeGates]
      split_ifs with hk
      · refine List.Pairwise.cons (fun b hb => ?_) ih
        obtain ⟨i, hi1, hi2, hi3⟩ := treeGates_support h k b hb
        rw [Finset.disjoint_left]
        intro a ha hb'
        rw [hi3 a] at hb'
        simp only [Instr.support, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at ha
        omega
      · exact ih

/-- One layer doubles an initial segment of wires. -/
theorem coneStep_treeGates {n t : ℕ} (h : 2 ^ t + 2 ^ t ≤ n) (k : ℕ) (hk : k ≤ 2 ^ t) :
    coneStep (treeGates t h k) (initSeg (2 ^ t)) = initSeg (2 ^ t + k) := by
  classical
  have hmeet : ∀ g ∈ treeGates t h k, (g.support ∩ initSeg (n := n) (2 ^ t)).Nonempty := by
    intro g hg
    obtain ⟨i, hi1, hi2, hi3⟩ := treeGates_support h k g hg
    refine ⟨⟨i, by omega⟩, Finset.mem_inter.2 ⟨(hi3 _).2 (Or.inl rfl), ?_⟩⟩
    rw [mem_initSeg]
    exact hi2
  rw [coneStep_of_all_meet _ _ hmeet]
  ext a
  rw [mem_foldr_union, mem_initSeg, mem_initSeg]
  constructor
  · rintro (hlt | ⟨g, hg, hga⟩)
    · omega
    · obtain ⟨i, hi1, hi2, hi3⟩ := treeGates_support h k g hg
      rcases (hi3 a).1 hga with hv | hv <;> omega
  · intro hlt
    by_cases hsmall : (a : ℕ) < 2 ^ t
    · exact Or.inl hsmall
    · exact Or.inr (exists_mem_treeGates h k hk ((a : ℕ) - 2 ^ t) (by omega) a (by omega))

/-! ### The binary tree circuit -/

/-- A depth-`d` CNOT binary tree on `n ≥ 2 ^ d` wires. Layer `t` is emitted so that the cone,
propagated backwards, is exactly the first `2 ^ t` wires after `t` layers. -/
def treeCirc {n : ℕ} : ∀ (d : ℕ), 2 ^ d ≤ n → Layered n
  | 0, _ => []
  | (d + 1), h =>
      treeGates d (by rw [pow_succ] at h; omega) (2 ^ d)
        :: treeCirc d (by rw [pow_succ] at h; omega)

theorem depth_treeCirc {n : ℕ} : ∀ (d : ℕ) (h : 2 ^ d ≤ n), depth (treeCirc d h) = d := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih => intro h; rw [treeCirc]; simpa [depth] using ih _

theorem layerOk_treeCirc {n : ℕ} : ∀ (d : ℕ) (h : 2 ^ d ≤ n), ∀ l ∈ treeCirc d h, LayerOk l := by
  intro d
  induction d with
  | zero => intro _ l hl; simp [treeCirc] at hl
  | succ d ih =>
      intro h l hl
      rw [treeCirc] at hl
      rcases List.mem_cons.1 hl with rfl | hl'
      · exact layerOk_treeGates _ _
      · exact ih _ l hl'

/-- The cone of the output wire, after `d` layers, is exactly the first `2 ^ d` wires. -/
theorem coneOf_treeCirc {n : ℕ} : ∀ (d : ℕ) (h : 2 ^ d ≤ n),
    coneOf (treeCirc d h) (initSeg 1) = initSeg (2 ^ d) := by
  intro d
  induction d with
  | zero => intro _; simp [treeCirc, coneOf_nil]
  | succ d ih =>
      intro h
      have hd : 2 ^ d + 2 ^ d ≤ n := by rw [pow_succ] at h; omega
      rw [treeCirc, coneOf_cons, ih]
      rw [coneStep_treeGates hd (2 ^ d) le_rfl, pow_succ]
      congr 1
      ring

theorem card_coneOf_treeCirc {n : ℕ} (d : ℕ) (h : 2 ^ d ≤ n) :
    (coneOf (treeCirc d h) (initSeg 1)).card = 2 ^ d := by
  rw [coneOf_treeCirc d h, card_initSeg h]

/-- **Sharpness.** For every depth `d` there is a well-formed depth-`d` circuit and a
single-wire set whose cone has exactly `2 ^ d` elements, so the bound `card_coneOf_le` is
attained and its exponent cannot be lowered. -/
theorem card_coneOf_le_isTight (d : ℕ) :
    ∃ (n : ℕ) (c : Layered n) (S : Finset (Fin n)),
      (∀ l ∈ c, LayerOk l) ∧ depth c = d ∧ S.card = 1 ∧
        (coneOf c S).card = 2 ^ depth c * S.card := by
  have hone : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  refine ⟨2 ^ d, treeCirc d le_rfl, initSeg 1, layerOk_treeCirc d le_rfl,
    depth_treeCirc d le_rfl, card_initSeg hone, ?_⟩
  rw [card_coneOf_treeCirc d le_rfl, depth_treeCirc d le_rfl, card_initSeg hone, mul_one]

/-! ## Closure under complement

Appending a bit flip on the output wire complements the acceptance probability. This is the
circuit-level content of `BQP = co-BQP`: the complement of a language decided with bounded
error is decided with the same error bound, by a well-formed circuit one layer deeper. -/

/-- Flipping wire `i` is an involution of basis strings. -/
def flipEquiv {n : ℕ} (i : Fin n) : Bits n ≃ Bits n where
  toFun y := Function.update y i (!(y i))
  invFun y := Function.update y i (!(y i))
  left_inv y := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  right_inv y := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_of_ne hk]

theorem flipEquiv_apply {n : ℕ} (i : Fin n) (y : Bits n) :
    flipEquiv i y = Function.update y i (!(y i)) := rfl

theorem flipEquiv_at {n : ℕ} (i : Fin n) (y : Bits n) : (flipEquiv i y) i = !(y i) := by
  simp [flipEquiv_apply]

/-- `X` on wire `i` permutes basis strings by flipping that wire. -/
theorem apply1_xMat {n : ℕ} (i : Fin n) (φ : QState n) (y : Bits n) :
    apply1 xMat i φ y = φ (flipEquiv i y) := by
  unfold apply1
  rw [flipEquiv_apply]
  cases hyi : y i <;> simp [xMat, hyi, Fintype.sum_bool]

theorem layerOk_singleton {n : ℕ} (g : Instr n) : LayerOk [g] := by
  simp [LayerOk]

/-- Appending an `X` on the output wire complements the acceptance probability. -/
theorem acceptProb_append_x {n m : ℕ} (c : Layered (n + m)) (x : Bits n) (out : Fin (n + m)) :
    acceptProb (c ++ [[Instr.x out]]) x out = 1 - acceptProb c x out := by
  classical
  have hrun : runLayered (c ++ [[Instr.x out]]) (inputState (m := m) x)
      = apply1 xMat out (runLayered c (inputState (m := m) x)) := by
    rw [runLayered_append]; rfl
  unfold acceptProb
  rw [hrun]
  set φ := runLayered c (inputState (m := m) x) with hφ
  have htotal : ∑ y : Bits (n + m), ‖φ y‖ ^ 2 = 1 := by
    rw [hφ, runLayered_norm]; exact inputState_norm x
  have step1 : ∀ y : Bits (n + m),
      (if y out then ‖apply1 xMat out φ y‖ ^ 2 else 0)
        = (if (flipEquiv out y) out then (0 : ℝ) else ‖φ (flipEquiv out y)‖ ^ 2) := by
    intro y
    rw [apply1_xMat, flipEquiv_at]
    cases hy : y out <;> simp
  rw [Finset.sum_congr rfl (fun y _ => step1 y)]
  rw [Fintype.sum_equiv (flipEquiv out)
        (fun y : Bits (n + m) =>
          if (flipEquiv out y) out then (0 : ℝ) else ‖φ (flipEquiv out y)‖ ^ 2)
        (fun y : Bits (n + m) => if y out then (0 : ℝ) else ‖φ y‖ ^ 2)
        (fun y => rfl)]
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Eq.trans ?_ htotal
  exact Finset.sum_congr rfl (fun y _ => by cases hy : y out <;> simp)

/-- **Closure under complement**, packaged: from any well-formed circuit there is a
well-formed circuit one layer deeper whose acceptance probability is the complement. -/
theorem exists_complement_circuit {n m : ℕ} (c : Layered (n + m)) (out : Fin (n + m))
    (hc : ∀ l ∈ c, LayerOk l) :
    ∃ c' : Layered (n + m), (∀ l ∈ c', LayerOk l) ∧ depth c' = depth c + 1 ∧
      ∀ x : Bits n, acceptProb c' x out = 1 - acceptProb c x out := by
  refine ⟨c ++ [[Instr.x out]], ?_, ?_, fun x => acceptProb_append_x c x out⟩
  · intro l hl
    rcases List.mem_append.1 hl with h1 | h2
    · exact hc l h1
    · rw [List.mem_singleton.1 h2]
      exact layerOk_singleton _
  · simp [depth_append, depth]

/-! ## A depth lower bound

Restating the counting bound as a lower bound on depth: a circuit all of whose input wires
are relevant to the output must be at least `log2 n` deep. -/

theorem log_le_depth_of_all_relevant {n m : ℕ} (c : Layered (n + m))
    (out : Fin (n + m)) (hc : ∀ l ∈ c, LayerOk l)
    (hall : ∀ i : Fin n, Fin.castAdd m i ∈ coneOf c {out}) :
    Nat.log 2 n ≤ depth c := by
  have h := card_le_two_pow_depth_of_all_relevant c out hc hall
  calc Nat.log 2 n ≤ Nat.log 2 (2 ^ depth c) := Nat.log_mono_right h
    _ = depth c := Nat.log_pow (by norm_num) _

/-! ## Heisenberg picture: operators supported on a wire set

The route to the semantic cone theorem. Rather than pushing states forward, conjugate the
measurement observable backwards through the circuit and track *where it is supported*; the
support grows by exactly one `coneStep` per layer. All claims below were checked numerically
against explicit matrices before being stated. -/

/-- An operator on `n` qubits. -/
abbrev Op (n : ℕ) := Matrix (Bits n) (Bits n) ℂ

/-- Overwrite `v` on `S` with the values carried by `w`. -/
def graft {n : ℕ} (S : Finset (Fin n)) (v : Bits n)
    (w : {k : Fin n // k ∈ S} → Bool) : Bits n :=
  fun k => if h : k ∈ S then w ⟨k, h⟩ else v k

theorem graft_of_mem {n : ℕ} (S : Finset (Fin n)) (v : Bits n)
    (w : {k : Fin n // k ∈ S} → Bool) {k : Fin n} (h : k ∈ S) :
    graft S v w k = w ⟨k, h⟩ := dif_pos h

theorem graft_of_not_mem {n : ℕ} (S : Finset (Fin n)) (v : Bits n)
    (w : {k : Fin n // k ∈ S} → Bool) {k : Fin n} (h : k ∉ S) :
    graft S v w k = v k := dif_neg h

theorem graft_injective {n : ℕ} (S : Finset (Fin n)) (v : Bits n) :
    Function.Injective (graft S v) := by
  intro w w' hw
  funext k
  have hk := congrFun hw k.1
  rw [graft_of_mem S v w k.2, graft_of_mem S v w' k.2] at hk
  simpa using hk

/-- A sum whose summand vanishes off the fibre `{u | u = v outside S}` collapses to a sum over
the values on `S` alone. This is the workhorse for the Heisenberg computations: it turns a sum
over all of `Bits n` into a sum over a gate's own wires. -/
theorem sum_of_vanishing {n : ℕ} (S : Finset (Fin n)) (v : Bits n) (F : Bits n → ℂ)
    (hF : ∀ u : Bits n, (¬ ∀ k, k ∉ S → u k = v k) → F u = 0) :
    ∑ u : Bits n, F u = ∑ w : {k : Fin n // k ∈ S} → Bool, F (graft S v w) := by
  classical
  have himg : ∑ w : {k : Fin n // k ∈ S} → Bool, F (graft S v w)
      = ∑ u ∈ Finset.image (graft S v) Finset.univ, F u :=
    (Finset.sum_image (fun a _ b _ h => graft_injective S v h)).symm
  rw [himg]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro u _ hu
  refine hF u ?_
  intro hagree
  refine hu (Finset.mem_image.2 ⟨fun k => u k.1, Finset.mem_univ _, ?_⟩)
  funext k
  by_cases hk : k ∈ S
  · rw [graft_of_mem S v _ hk]
  · rw [graft_of_not_mem S v _ hk]; exact (hagree k hk).symm

/-- `A` acts as the identity outside `S`: entries vanish unless the two basis strings agree
off `S`, and otherwise depend only on the restrictions to `S`. This is the tensor-product
condition `A = A_S ⊗ I`, written without tensor products.

Stated as a conjunction rather than as `∃ B, ...` because both halves are used directly in the
conjugation lemmas below, where reconstructing a full basis string from a restriction would
otherwise be needed inside a double sum. -/
def IsLocal {n : ℕ} (S : Finset (Fin n)) (A : Op n) : Prop :=
  (∀ y z : Bits n, (¬ ∀ k, k ∉ S → y k = z k) → A y z = 0) ∧
  (∀ y z y' z' : Bits n, (∀ k ∈ S, y k = y' k) → (∀ k ∈ S, z k = z' k) →
      (∀ k, k ∉ S → y k = z k) → (∀ k, k ∉ S → y' k = z' k) → A y z = A y' z')

theorem IsLocal.vanish {n : ℕ} {S : Finset (Fin n)} {A : Op n} (h : IsLocal S A)
    {y z : Bits n} (hne : ¬ ∀ k, k ∉ S → y k = z k) : A y z = 0 := h.1 y z hne

theorem IsLocal.entry_congr {n : ℕ} {S : Finset (Fin n)} {A : Op n} (h : IsLocal S A)
    {y z y' z' : Bits n} (hy : ∀ k ∈ S, y k = y' k) (hz : ∀ k ∈ S, z k = z' k)
    (hyz : ∀ k, k ∉ S → y k = z k) (hyz' : ∀ k, k ∉ S → y' k = z' k) :
    A y z = A y' z' := h.2 y z y' z' hy hz hyz hyz'

/-- The payoff: a diagonal entry of an `S`-local operator depends only on the restriction of
the basis string to `S`. This is the step that turns cone-locality into target 3. -/
theorem IsLocal.diag_congr {n : ℕ} {S : Finset (Fin n)} {A : Op n} (h : IsLocal S A)
    {x x' : Bits n} (hx : ∀ k ∈ S, x k = x' k) : A x x = A x' x' :=
  h.entry_congr hx hx (fun _ _ => rfl) (fun _ _ => rfl)

/-- Locality to a larger set is a weaker statement. -/
theorem IsLocal.mono {n : ℕ} {S S' : Finset (Fin n)} {A : Op n} (hSS : S ⊆ S')
    (h : IsLocal S A) : IsLocal S' A := by
  have out : ∀ {k : Fin n}, k ∉ S' → k ∉ S := fun {_} hk hk' => hk (hSS hk')
  refine ⟨fun y z hne => h.vanish (fun hag => hne (fun k hk => hag k (out hk))),
    fun y z y' z' hy hz hyz hyz' => ?_⟩
  have hequiv : (∀ k, k ∉ S → y k = z k) ↔ (∀ k, k ∉ S → y' k = z' k) := by
    constructor
    · intro hag k hk
      by_cases hk' : k ∈ S'
      · rw [← hy k hk', ← hz k hk']; exact hag k hk
      · exact hyz' k hk'
    · intro hag k hk
      by_cases hk' : k ∈ S'
      · rw [hy k hk', hz k hk']; exact hag k hk
      · exact hyz k hk'
  by_cases hoff : ∀ k, k ∉ S → y k = z k
  · exact h.entry_congr (fun k hk => hy k (hSS hk)) (fun k hk => hz k (hSS hk))
      hoff (hequiv.1 hoff)
  · rw [h.vanish hoff, h.vanish (fun hc => hoff (hequiv.2 hc))]

/-- Matrix of a one-qubit gate on wire `i`, written so that `{i}`-locality is manifest. -/
def apply1Matrix {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n) : Op n :=
  Matrix.of fun y z =>
    if (∀ k, k ∉ ({i} : Finset (Fin n)) → y k = z k) then U (y i) (z i) else 0

/-- Matrix of CNOT (control `i`, target `j`), written so that `{i,j}`-locality is manifest. -/
def cnotMatrix {n : ℕ} (i j : Fin n) : Op n :=
  Matrix.of fun y z =>
    if (∀ k, k ∉ ({i, j} : Finset (Fin n)) → y k = z k) ∧ z i = y i ∧ z j = xor (y j) (y i)
    then 1 else 0

/-- H1 for one-qubit gates. -/
theorem isLocal_apply1Matrix {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n) :
    IsLocal {i} (apply1Matrix U i) := by
  refine ⟨fun y z hne => by simp only [apply1Matrix, Matrix.of_apply, if_neg hne],
    fun y z y' z' hy hz hyz hyz' => ?_⟩
  have hi : i ∈ ({i} : Finset (Fin n)) := Finset.mem_singleton_self i
  simp only [apply1Matrix, Matrix.of_apply, if_pos hyz, if_pos hyz', hy i hi, hz i hi]

/-- H1 for CNOT. -/
theorem isLocal_cnotMatrix {n : ℕ} (i j : Fin n) :
    IsLocal {i, j} (cnotMatrix i j) := by
  have hi : i ∈ ({i, j} : Finset (Fin n)) := Finset.mem_insert_self i {j}
  have hj : j ∈ ({i, j} : Finset (Fin n)) := Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
  refine ⟨fun y z hne => ?_, fun y z y' z' hy hz hyz hyz' => ?_⟩
  · simp only [cnotMatrix, Matrix.of_apply]
    exact if_neg (fun hc => hne hc.1)
  · simp only [cnotMatrix, Matrix.of_apply, hy i hi, hy j hj, hz i hi, hz j hj,
      iff_of_true hyz hyz']

/-! ### The gate matrices implement the gate semantics -/

theorem apply1_eq_mulVec {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n) (ψ : QState n) :
    apply1 U i ψ = (apply1Matrix U i).mulVec ψ := by
  classical
  funext y
  have main : (apply1Matrix U i).mulVec ψ y
      = ∑ z ∈ Finset.univ.filter
          (fun z : Bits n => ∀ k, k ∉ ({i} : Finset (Fin n)) → y k = z k),
          U (y i) (z i) * ψ z := by
    unfold Matrix.mulVec dotProduct apply1Matrix
    simp only [Matrix.of_apply, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun z _ => by split <;> simp)
  have himg : Finset.univ.filter
        (fun z : Bits n => ∀ k, k ∉ ({i} : Finset (Fin n)) → y k = z k)
      = Finset.image (fun b : Bool => Function.update y i b) Finset.univ := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine ⟨z i, ?_⟩
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · rw [Function.update_of_ne hk]; exact h k (by simpa using hk)
    · rintro ⟨b, -, rfl⟩ k hk
      exact (Function.update_of_ne (by simpa using hk) _ _).symm
  rw [main, himg, Finset.sum_image (by
        intro a _ b _ hab; simpa using congrFun hab i)]
  unfold apply1
  exact Finset.sum_congr rfl (fun b _ => by rw [Function.update_self])

theorem cnotState_eq_mulVec {n : ℕ} (i j : Fin n) (hij : i ≠ j) (ψ : QState n) :
    cnotState i j hij ψ = (cnotMatrix i j).mulVec ψ := by
  classical
  funext y
  unfold Matrix.mulVec dotProduct cnotMatrix cnotState
  simp only [Matrix.of_apply]
  rw [Finset.sum_eq_single (Function.update y j (xor (y j) (y i)))]
  · rw [if_pos, one_mul]
    refine ⟨fun k hk => ?_, ?_, ?_⟩
    · have hkj : k ≠ j := by intro h; exact hk (by simp [h])
      exact (Function.update_of_ne hkj _ _).symm
    · exact Function.update_of_ne hij _ _
    · exact Function.update_self _ _ _
  · intro z _ hz
    rw [if_neg, zero_mul]
    rintro ⟨hoff, hi, hj⟩
    refine hz ?_
    funext k
    by_cases hk : k = j
    · subst hk; rw [Function.update_self]; exact hj
    · rw [Function.update_of_ne hk]
      by_cases hki : k = i
      · subst hki; exact hi
      · exact (hoff k (by simp [hk, hki])).symm
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The matrix of an instruction. -/
noncomputable def gateMatrix {n : ℕ} : Instr n → Op n
  | .h i => apply1Matrix hMat i
  | .s i => apply1Matrix sMat i
  | .t i => apply1Matrix tMat i
  | .x i => apply1Matrix xMat i
  | .cnot i j _ => cnotMatrix i j

theorem Instr.apply_eq_mulVec {n : ℕ} (g : Instr n) (ψ : QState n) :
    g.apply ψ = (gateMatrix g).mulVec ψ := by
  cases g with
  | h i => exact apply1_eq_mulVec hMat i ψ
  | s i => exact apply1_eq_mulVec sMat i ψ
  | t i => exact apply1_eq_mulVec tMat i ψ
  | x i => exact apply1_eq_mulVec xMat i ψ
  | cnot i j hij => exact cnotState_eq_mulVec i j hij ψ

/-- H1: each gate matrix is local to the gate's support. -/
theorem isLocal_gateMatrix {n : ℕ} (g : Instr n) : IsLocal g.support (gateMatrix g) := by
  cases g with
  | h i => exact isLocal_apply1Matrix hMat i
  | s i => exact isLocal_apply1Matrix sMat i
  | t i => exact isLocal_apply1Matrix tMat i
  | x i => exact isLocal_apply1Matrix xMat i
  | cnot i j hij => exact isLocal_cnotMatrix i j


end ShiShallow

open ShiShallow

theorem solution {n : ℕ} (c : Layered n) (hc : ∀ l ∈ c, LayerOk l) (S : Finset (Fin n)) :
    (coneOf c S).card ≤ 2 ^ depth c * S.card := card_coneOf_le c hc S
