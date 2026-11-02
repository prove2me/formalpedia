-- Prove2me | solution 1 for QAlgorithms.LearningSurvey.servedioGortler_classical_le_cube
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:01:25.681304+00:00
-- url     : https://prove2.me/submissions/c05d99e9-ea84-4da4-aff3-d308eaa9a08f

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
import Theorems.Thm_QAlgorithms_LearningSurvey_servedioGortler_quantum_lower
set_option autoImplicit false

open scoped BigOperators ENNReal Matrix ComplexConjugate
open QAlgorithms
open QAlgorithms.Learning
open QAlgorithms.LearningSurvey

noncomputable section

namespace SolServedioCube

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def bestQueryIdx [Nonempty ι] (C' : Finset (ι → Bool)) : ι :=
  (Finset.exists_max_image Finset.univ
    (fun i : ι => min (gammaFrac C' i false) (gammaFrac C' i true))
    Finset.univ_nonempty).choose

private lemma bestQueryIdx_spec [Nonempty ι] (C' : Finset (ι → Bool)) (j : ι) :
    min (gammaFrac C' j false) (gammaFrac C' j true) ≤
      min (gammaFrac C' (bestQueryIdx C') false) (gammaFrac C' (bestQueryIdx C') true) := by
  exact (Finset.exists_max_image Finset.univ
    (fun i : ι => min (gammaFrac C' i false) (gammaFrac C' i true))
    Finset.univ_nonempty).choose_spec.2 j (Finset.mem_univ j)

private lemma gammaPrime_le_bestQueryIdx [Nonempty ι] (C' : Finset (ι → Bool)) :
    gammaPrime C' ≤
      min (gammaFrac C' (bestQueryIdx C') false) (gammaFrac C' (bestQueryIdx C') true) := by
  unfold gammaPrime
  exact ciSup_le (bestQueryIdx_spec C')

private def buildTree [Nonempty ι] : ℕ → Finset (ι → Bool) → DecisionTree ι Bool (ι → Bool)
  | 0, C' =>
      DecisionTree.leaf (if h : C'.Nonempty then h.choose else fun _ => false)
  | fuel + 1, C' =>
      if 2 ≤ C'.card then
        let i := bestQueryIdx C'
        DecisionTree.node i (fun b => buildTree fuel (C'.filter fun c => c i = b))
      else
        DecisionTree.leaf (if h : C'.Nonempty then h.choose else fun _ => false)

private lemma buildTree_queries_le [Nonempty ι] :
    ∀ (fuel : ℕ) (C' : Finset (ι → Bool)) (x : ι → Bool),
      (buildTree fuel C').queries x ≤ fuel
  | 0, C', x => by simp [buildTree, DecisionTree.queries]
  | fuel + 1, C', x => by
    unfold buildTree
    by_cases h2 : 2 ≤ C'.card
    · rw [if_pos h2]
      simp only [DecisionTree.queries]
      have h := buildTree_queries_le fuel (C'.filter fun c => c (bestQueryIdx C') = x (bestQueryIdx C')) x
      omega
    · rw [if_neg h2]
      simp [DecisionTree.queries]

private lemma filter_bool_add_card (C' : Finset (ι → Bool)) (i : ι) (b : Bool) :
    (C'.filter fun c => c i = b).card + (C'.filter fun c => c i = !b).card = C'.card := by
  have h := Finset.card_filter_add_card_filter_not (s := C') (p := fun c : ι → Bool => c i = b)
  have hnot : (C'.filter fun c : ι → Bool => ¬c i = b) = C'.filter fun c => c i = !b := by
    ext c
    cases hci : c i <;> cases b <;> simp [hci]
  rw [hnot] at h
  exact h

private lemma gammaFrac_le_one (C' : Finset (ι → Bool)) (i : ι) (b : Bool) :
    gammaFrac C' i b ≤ 1 := by
  unfold gammaFrac
  by_cases h0 : C'.card = 0
  · simp [h0]
  · have hpos : (0 : ℝ) < (C'.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
    rw [div_le_one hpos]
    exact Nat.cast_le.mpr (Finset.card_filter_le _ _)

private lemma gammaPrime_le_one [Nonempty ι] (C' : Finset (ι → Bool)) :
    gammaPrime C' ≤ 1 := by
  unfold gammaPrime
  refine ciSup_le fun i => ?_
  exact le_trans (min_le_left _ _) (gammaFrac_le_one C' i false)

private lemma gammaParam_le_of_subset [Nonempty ι] {C C' : Finset (ι → Bool)}
    (hsub : C' ⊆ C) (hcard : 2 ≤ C'.card) :
    gammaParam C ≤ gammaPrime C' := by
  unfold gammaParam
  have hbdd : BddBelow (Set.range fun S : {C' : Finset (ι → Bool) // C' ⊆ C ∧ 2 ≤ C'.card} =>
      gammaPrime S.1) := Set.Finite.bddBelow (Set.toFinite _)
  exact ciInf_le hbdd ⟨C', hsub, hcard⟩

private lemma gammaParam_le_one [Nonempty ι] {C : Finset (ι → Bool)} (hC : 2 ≤ C.card) :
    gammaParam C ≤ 1 :=
  le_trans (gammaParam_le_of_subset (Finset.Subset.refl C) hC) (gammaPrime_le_one C)

private lemma gammaPrime_pos_of_two_le [Nonempty ι] {C' : Finset (ι → Bool)} (hcard : 2 ≤ C'.card) :
    0 < gammaPrime C' := by
  have h1 : 1 < C'.card := by omega
  obtain ⟨c₁, hc₁, c₂, hc₂, hne⟩ := Finset.one_lt_card.mp h1
  have hex : ∃ i : ι, c₁ i ≠ c₂ i := by
    by_contra hall
    apply hne
    ext i
    exact Classical.not_not.mp fun h => hall ⟨i, h⟩
  obtain ⟨i₀, hi₀⟩ := hex
  have hfalse_pos : 1 ≤ (C'.filter fun c => c i₀ = false).card := by
    cases h1i : c₁ i₀
    · exact Finset.card_pos.mpr ⟨c₁, Finset.mem_filter.mpr ⟨hc₁, h1i⟩⟩
    · have h2i : c₂ i₀ = false := by
        cases h2 : c₂ i₀
        · rfl
        · exfalso; exact hi₀ (h1i.trans h2.symm)
      exact Finset.card_pos.mpr ⟨c₂, Finset.mem_filter.mpr ⟨hc₂, h2i⟩⟩
  have htrue_pos : 1 ≤ (C'.filter fun c => c i₀ = true).card := by
    cases h1i : c₁ i₀
    · have h2i : c₂ i₀ = true := by
        cases h2 : c₂ i₀
        · exfalso; exact hi₀ (h1i.trans h2.symm)
        · rfl
      exact Finset.card_pos.mpr ⟨c₂, Finset.mem_filter.mpr ⟨hc₂, h2i⟩⟩
    · exact Finset.card_pos.mpr ⟨c₁, Finset.mem_filter.mpr ⟨hc₁, h1i⟩⟩
  have hcard_pos : (0 : ℝ) < (C'.card : ℝ) := Nat.cast_pos.mpr (by omega)
  have hf : 0 < gammaFrac C' i₀ false := by
    unfold gammaFrac
    refine div_pos ?_ hcard_pos
    exact Nat.cast_pos.mpr (by omega)
  have ht : 0 < gammaFrac C' i₀ true := by
    unfold gammaFrac
    refine div_pos ?_ hcard_pos
    exact Nat.cast_pos.mpr (by omega)
  have hmin : 0 < min (gammaFrac C' i₀ false) (gammaFrac C' i₀ true) := lt_min hf ht
  exact lt_of_lt_of_le hmin (le_trans (bestQueryIdx_spec C' i₀) (by
    unfold gammaPrime
    have hbdd : BddAbove (Set.range fun i : ι => min (gammaFrac C' i false) (gammaFrac C' i true)) :=
      Set.Finite.bddAbove (Set.toFinite _)
    exact le_ciSup hbdd (bestQueryIdx C')))

private lemma gammaParam_pos [Nonempty ι] {C : Finset (ι → Bool)} (hC : 2 ≤ C.card) :
    0 < gammaParam C := by
  unfold gammaParam
  have : Nonempty {C' : Finset (ι → Bool) // C' ⊆ C ∧ 2 ≤ C'.card} :=
    ⟨⟨C, Finset.Subset.refl C, hC⟩⟩
  obtain ⟨S, hS⟩ := exists_eq_ciInf_of_finite (f := fun S : {C' : Finset (ι → Bool) // C' ⊆ C ∧ 2 ≤ C'.card} =>
    gammaPrime S.1)
  rw [← hS]
  exact gammaPrime_pos_of_two_le S.2.2

private lemma filter_card_le_one_sub_gammaParam [Nonempty ι] {C C' : Finset (ι → Bool)}
    (hsub : C' ⊆ C) (hcard : 2 ≤ C'.card) (b : Bool) :
    ((C'.filter fun c => c (bestQueryIdx C') = b).card : ℝ) ≤
      (C'.card : ℝ) * (1 - gammaParam C) := by
  let i := bestQueryIdx C'
  have hγ : gammaParam C ≤ min (gammaFrac C' i false) (gammaFrac C' i true) :=
    le_trans (gammaParam_le_of_subset hsub hcard) (gammaPrime_le_bestQueryIdx C')
  have hfrac : gammaParam C ≤ gammaFrac C' i (!b) := by
    cases b
    · exact le_trans hγ (min_le_right _ _)
    · exact le_trans hγ (min_le_left _ _)
  unfold gammaFrac at hfrac
  have hpos : (0 : ℝ) < (C'.card : ℝ) := Nat.cast_pos.mpr (by omega)
  have hmul : gammaParam C * (C'.card : ℝ) ≤ ((C'.filter fun c => c i = !b).card : ℝ) :=
    (le_div_iff₀ hpos).mp hfrac
  have hsum : ((C'.filter fun c => c i = b).card : ℝ) +
      ((C'.filter fun c => c i = !b).card : ℝ) = (C'.card : ℝ) := by
    exact_mod_cast filter_bool_add_card C' i b
  linarith

private lemma buildTree_eval_eq [Nonempty ι] {C : Finset (ι → Bool)} (hC2 : 2 ≤ C.card) :
    ∀ (fuel : ℕ) (C' : Finset (ι → Bool)),
      C' ⊆ C →
      (C'.card : ℝ) * (1 - gammaParam C) ^ fuel < 2 →
      ∀ c ∈ C', (buildTree fuel C').eval c = c
  | 0, C', _, hlt, c, hc => by
    simp only [pow_zero, mul_one] at hlt
    have hcard1 : C'.card ≤ 1 := by
      have : C'.card < 2 := by exact_mod_cast hlt
      omega
    have hne : C'.Nonempty := ⟨c, hc⟩
    unfold buildTree DecisionTree.eval
    rw [dif_pos hne]
    exact Finset.card_le_one.mp hcard1 hne.choose hne.choose_spec c hc
  | fuel + 1, C', hsub, hlt, c, hc => by
    unfold buildTree
    by_cases h2 : 2 ≤ C'.card
    · rw [if_pos h2]
      simp only [DecisionTree.eval]
      let C'' := C'.filter fun c' => c' (bestQueryIdx C') = c (bestQueryIdx C')
      have hc'' : c ∈ C'' := Finset.mem_filter.mpr ⟨hc, rfl⟩
      have hsub'' : C'' ⊆ C := Finset.Subset.trans (Finset.filter_subset _ _) hsub
      have hcard'' : (C''.card : ℝ) ≤ (C'.card : ℝ) * (1 - gammaParam C) :=
        filter_card_le_one_sub_gammaParam hsub h2 (c (bestQueryIdx C'))
      have h1_nonneg : 0 ≤ 1 - gammaParam C := by
        have := gammaParam_le_one hC2
        linarith
      have hpow_nonneg : 0 ≤ (1 - gammaParam C) ^ fuel := pow_nonneg h1_nonneg fuel
      have hlt'' : (C''.card : ℝ) * (1 - gammaParam C) ^ fuel < 2 := by
        calc (C''.card : ℝ) * (1 - gammaParam C) ^ fuel
            ≤ ((C'.card : ℝ) * (1 - gammaParam C)) * (1 - gammaParam C) ^ fuel :=
              mul_le_mul_of_nonneg_right hcard'' hpow_nonneg
          _ = (C'.card : ℝ) * (1 - gammaParam C) ^ (fuel + 1) := by rw [pow_succ', mul_assoc]
          _ < 2 := hlt
      exact buildTree_eval_eq hC2 fuel C'' hsub'' hlt'' c hc''
    · rw [if_neg h2]
      simp only [DecisionTree.eval]
      have hcard1 : C'.card ≤ 1 := by omega
      have hne : C'.Nonempty := ⟨c, hc⟩
      rw [dif_pos hne]
      exact Finset.card_le_one.mp hcard1 hne.choose hne.choose_spec c hc

private lemma classicalExactComplexity_le_of_tree {C : Finset (ι → Bool)} {T : ℕ}
    (t : DecisionTree ι Bool (ι → Bool))
    (hq : ∀ x : ι → Bool, t.queries x ≤ T)
    (heval : ∀ c ∈ C, t.eval c = c) :
    classicalExactComplexity C ≤ T := by
  unfold classicalExactComplexity
  refine Nat.sInf_le ⟨PMF.pure t, ?_, ?_⟩
  · intro t' ht' x
    rw [PMF.support_pure, Set.mem_singleton_iff] at ht'
    subst ht'
    exact hq x
  · intro c hc
    simp [successProb, PMF.pure_map, heval c hc]
    norm_num

private lemma classicalExactComplexity_eq_zero_of_card_le_one {C : Finset (ι → Bool)}
    (hC : C.card ≤ 1) :
    classicalExactComplexity C = 0 := by
  have hle : classicalExactComplexity C ≤ 0 := by
    refine classicalExactComplexity_le_of_tree
      (DecisionTree.leaf (if h : C.Nonempty then h.choose else fun _ => false))
      (fun _ => le_rfl) ?_
    intro c hc
    have hne : C.Nonempty := ⟨c, hc⟩
    simp only [DecisionTree.eval, dif_pos hne]
    exact Finset.card_le_one.mp hC hne.choose hne.choose_spec c hc
  omega

private lemma classicalExactComplexity_le_log_div_gamma [Nonempty ι] {C : Finset (ι → Bool)}
    (hC2 : 2 ≤ C.card) :
    (classicalExactComplexity C : ℝ) ≤ Real.log (C.card : ℝ) / gammaParam C + 1 := by
  have hγ_pos : 0 < gammaParam C := gammaParam_pos hC2
  have hγ_le_one : gammaParam C ≤ 1 := gammaParam_le_one hC2
  let fuel : ℕ := Nat.floor (Real.log (C.card : ℝ) / gammaParam C) + 1
  have hfuel_gt : Real.log (C.card : ℝ) / gammaParam C < (fuel : ℝ) := by
    dsimp [fuel]
    push_cast
    exact Nat.lt_floor_add_one (Real.log (C.card : ℝ) / gammaParam C)
  have hC_pos : (0 : ℝ) < (C.card : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlog_nonneg : 0 ≤ Real.log (C.card : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ C.card by omega)
  have hdiv_nonneg : 0 ≤ Real.log (C.card : ℝ) / gammaParam C :=
    div_nonneg hlog_nonneg (le_of_lt hγ_pos)
  have hfuel_le : (fuel : ℝ) ≤ Real.log (C.card : ℝ) / gammaParam C + 1 := by
    dsimp [fuel]
    push_cast
    linarith [Nat.floor_le hdiv_nonneg]
  have hlt2 : (C.card : ℝ) * (1 - gammaParam C) ^ fuel < 2 := by
    have h1_sub_le : 1 - gammaParam C ≤ Real.exp (-gammaParam C) := by
      have := Real.add_one_le_exp (-gammaParam C)
      linarith
    have h1_nonneg : 0 ≤ 1 - gammaParam C := by linarith
    have hpow_le : (1 - gammaParam C) ^ fuel ≤ Real.exp (-gammaParam C) ^ fuel :=
      pow_le_pow_left₀ h1_nonneg h1_sub_le fuel
    have hexp_pow : Real.exp (-gammaParam C) ^ fuel = Real.exp (-(fuel : ℝ) * gammaParam C) := by
      rw [← Real.exp_nat_mul]
      ring_nf
    have hmul_gt : Real.log (C.card : ℝ) < (fuel : ℝ) * gammaParam C :=
      (div_lt_iff₀ hγ_pos).mp hfuel_gt
    have hexp_lt : Real.exp (-(fuel : ℝ) * gammaParam C) < Real.exp (-Real.log (C.card : ℝ)) := by
      apply Real.exp_lt_exp.mpr
      linarith
    have hexp_neg_log : Real.exp (-Real.log (C.card : ℝ)) = (C.card : ℝ)⁻¹ := by
      rw [Real.exp_neg, Real.exp_log hC_pos]
    have hprod_lt_one : (C.card : ℝ) * (1 - gammaParam C) ^ fuel < 1 := by
      calc (C.card : ℝ) * (1 - gammaParam C) ^ fuel
          ≤ (C.card : ℝ) * Real.exp (-(fuel : ℝ) * gammaParam C) := by
            rw [← hexp_pow]
            exact mul_le_mul_of_nonneg_left hpow_le (le_of_lt hC_pos)
        _ < (C.card : ℝ) * (C.card : ℝ)⁻¹ := by
            rw [← hexp_neg_log]
            exact mul_lt_mul_of_pos_left hexp_lt hC_pos
        _ = 1 := mul_inv_cancel₀ (ne_of_gt hC_pos)
    linarith
  have htree_le : classicalExactComplexity C ≤ fuel :=
    classicalExactComplexity_le_of_tree (buildTree fuel C) (buildTree_queries_le fuel C)
      (buildTree_eval_eq hC2 fuel C (Finset.Subset.refl C) hlt2)
  exact le_trans (by exact_mod_cast htree_le) hfuel_le

/-! ### Explicit quantum exact learner querying all points -/

private def permMat {X : Type*} [DecidableEq X] (σ : X ≃ X) : Matrix X X ℂ :=
  Matrix.of fun x y => if x = σ y then 1 else 0

private lemma permMat_mem_unitary {X : Type*} [Fintype X] [DecidableEq X] (σ : X ≃ X) :
    permMat σ ∈ Matrix.unitaryGroup X ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext x y
  simp only [permMat, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply]
  rw [Finset.sum_eq_single (σ.symm x)]
  · simp only [σ.apply_symm_apply, ↓reduceIte, one_mul]
    by_cases hxy : x = y
    · subst hxy; simp
    · have hyx : y ≠ x := Ne.symm hxy
      simp [hxy, hyx]
  · intro z _ hz
    have hne : x ≠ σ z := fun h => hz (by rw [h, σ.symm_apply_apply])
    simp [hne]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

private lemma act_permMat_ket {X : Type*} [Fintype X] [DecidableEq X] (σ : X ≃ X) (y : X) :
    act (permMat σ) (ket y) = ket (σ y) := by
  ext x
  simp only [act, permMat, ket, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, Matrix.of_apply,
    PiLp.single_apply]
  rw [Finset.sum_eq_single y]
  · by_cases hx : x = σ y <;> simp [hx]
  · intro z _ hzy
    simp [hzy]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

private lemma act_kronecker_xorOracle_ket {W : Type*} [Fintype W] [DecidableEq W]
    (c : ι → Bool) (i : ι) (b : Bool) (w : W) :
    act (Matrix.kronecker (xorOracle c) (1 : Matrix W W ℂ)) (ket ((i, b), w)) =
      ket ((i, b + c i), w) := by
  ext ⟨⟨i', b'⟩, w'⟩
  simp only [act, xorOracle, ket, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct,
    PiLp.single_apply]
  rw [Finset.sum_eq_single ((i, b), w)]
  · by_cases hi : i' = i
    · subst hi
      by_cases hw : w' = w
      · subst hw
        rcases hci : c i' with _ | _ <;> cases b <;> cases b' <;>
          simp [Matrix.kroneckerMap_apply, Matrix.one_apply, hci]
      · simp [Matrix.kroneckerMap_apply, Matrix.one_apply, hw]
    · simp [Matrix.kroneckerMap_apply, Matrix.one_apply, hi]
  · rintro ⟨⟨i₂, b₂⟩, w₂⟩ _ hne
    simp [hne]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

private def storeBitEquiv : ((ι × Bool) × (ι → Bool)) ≃ ((ι × Bool) × (ι → Bool)) where
  toFun := fun ⟨⟨i, b⟩, w⟩ => ⟨⟨i, w i⟩, Function.update w i b⟩
  invFun := fun ⟨⟨i, b⟩, w⟩ => ⟨⟨i, w i⟩, Function.update w i b⟩
  left_inv := by
    rintro ⟨⟨i, b⟩, w⟩
    simp only [Function.update_self, Prod.mk.injEq, true_and]
    ext j
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji]
  right_inv := by
    rintro ⟨⟨i, b⟩, w⟩
    simp only [Function.update_self, Prod.mk.injEq, true_and]
    ext j
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji]

private lemma ket_norm_one {X : Type*} [Fintype X] [DecidableEq X] (x : X) :
    ‖(ket x : EuclideanSpace ℂ X)‖ = 1 := by
  have hsq : ‖(ket x : EuclideanSpace ℂ X)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    rw [Finset.sum_eq_single x]
    · simp [ket]
    · intro y _ hy
      simp [ket, hy]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  have h0 : 0 ≤ ‖(ket x : EuclideanSpace ℂ X)‖ := norm_nonneg _
  nlinarith

private lemma quantumExactComplexity_nonempty [Nonempty ι] (C : Finset (ι → Bool)) :
    {T : ℕ | ∃ (w : ℕ) (A : QueryAlg ι Bool (Fin w) T)
      (out : (ι × Bool) × Fin w → (ι → Bool)), IsQExactLearner A out C}.Nonempty := by
  classical
  let N := Fintype.card ι
  let e : Fin N ≃ ι := (Fintype.equivFin ι).symm
  let wCard := Fintype.card (ι → Bool)
  let ew : (ι → Bool) ≃ Fin wCard := Fintype.equivFin (ι → Bool)
  let i₀ : ι := Classical.arbitrary ι
  let idxAt : ℕ → ι := fun t => if h : t < N then e ⟨t, h⟩ else i₀
  let wAt : (ι → Bool) → ℕ → (ι → Bool) :=
    fun c t i => if (e.symm i : ℕ) < t then c i else false
  let stepEquiv : Fin N → ((ι × Bool) × Fin wCard) ≃ ((ι × Bool) × Fin wCard) :=
    fun s =>
      ((Equiv.prodCongr (Equiv.refl (ι × Bool)) ew.symm).trans storeBitEquiv).trans
        (Equiv.prodCongr
          (Equiv.prodCongr (Equiv.swap (e s) (idxAt (s.1 + 1))) (Equiv.refl Bool))
          ew)
  let U : Fin (N + 1) → Matrix.unitaryGroup ((ι × Bool) × Fin wCard) ℂ :=
    Fin.cases ⟨permMat (Equiv.refl _), permMat_mem_unitary (Equiv.refl _)⟩
      (fun s => ⟨permMat (stepEquiv s), permMat_mem_unitary (stepEquiv s)⟩)
  let A : QueryAlg ι Bool (Fin wCard) N :=
    { start := ket ((idxAt 0, false), ew (wAt (fun _ => false) 0))
      start_unit := ket_norm_one _
      U := U }
  have hstate : ∀ (c : ι → Bool) (t : Fin (N + 1)),
      A.stateAt (xorOracle c) t = ket ((idxAt t.1, false), ew (wAt c t.1)) := by
    intro c t
    refine Fin.induction ?_ ?_ t
    · change act (A.U 0 : Matrix _ _ ℂ) A.start = ket ((idxAt 0, false), ew (wAt c 0))
      have hw0 : wAt (fun _ => false) 0 = wAt c 0 := by
        ext i; simp [wAt]
      dsimp [A, U]
      rw [act_permMat_ket, Equiv.refl_apply, hw0]
    · intro s ih
      change act (A.U s.succ : Matrix _ _ ℂ)
        (act (Matrix.kronecker (xorOracle c) (1 : Matrix (Fin wCard) (Fin wCard) ℂ))
          (A.stateAt (xorOracle c) s.castSucc)) =
        ket ((idxAt (s.1 + 1), false), ew (wAt c (s.1 + 1)))
      rw [ih]
      simp only [Fin.coe_castSucc]
      have hidx_s : idxAt s.1 = e s := dif_pos s.2
      rw [hidx_s, act_kronecker_xorOracle_ket]
      have hb : (false + c (e s) : Bool) = c (e s) := by cases c (e s) <;> rfl
      rw [hb]
      dsimp [A, U]
      rw [act_permMat_ket]
      congr 1
      have hws : wAt c s.1 (e s) = false := by
        simp [wAt]
      have hw_upd : Function.update (wAt c s.1) (e s) (c (e s)) = wAt c (s.1 + 1) := by
        ext i
        by_cases hi : i = e s
        · subst hi
          simp [wAt]
        · have hne : (e.symm i : ℕ) ≠ s.1 := by
            intro hEq
            apply hi
            have h1 : e.symm i = s := Fin.ext hEq
            rw [← h1, e.apply_symm_apply]
          have hlt_iff : ((e.symm i : ℕ) < s.1 + 1) ↔ ((e.symm i : ℕ) < s.1) := by omega
          simp [Function.update_apply, hi, wAt, hlt_iff]
      simp [stepEquiv, storeBitEquiv, hws, hw_upd]
  refine ⟨N, wCard, A, fun z => ew.symm z.2, ?_⟩
  intro c _
  unfold QueryAlg.outputProb probEvent
  have hfin : A.finalState (xorOracle c) = ket ((idxAt N, false), ew c) := by
    unfold QueryAlg.finalState
    rw [hstate c (Fin.last N)]
    have hwN : wAt c N = c := by
      ext i
      simp [wAt, (e.symm i).2]
    simp [hwN]
  rw [hfin]
  let z₀ : (ι × Bool) × Fin wCard := ((idxAt N, false), ew c)
  have hz₀_mem : z₀ ∈ Finset.univ.filter (fun z : (ι × Bool) × Fin wCard => ew.symm z.2 = c) := by
    simp [z₀]
  have hle : prob (ket z₀) z₀ ≤
      ∑ z ∈ Finset.univ.filter (fun z : (ι × Bool) × Fin wCard => ew.symm z.2 = c),
        prob (ket z₀) z := by
    refine Finset.single_le_sum (fun z _ => ?_) hz₀_mem
    unfold prob
    positivity
  have hp1 : prob (ket z₀) z₀ = 1 := by
    simp [prob, ket]
  linarith

end SolServedioCube

theorem solution :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (C : Finset (Qubits n → Bool)),
      (Learning.classicalExactComplexity C : ℝ) ≤
        K * (n : ℝ) * (Learning.quantumExactComplexity C : ℝ) ^ 3 := by
  obtain ⟨K₁, hK₁_pos, hSG⟩ := QAlgorithms.LearningSurvey.servedioGortler_quantum_lower.{0}
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let K : ℝ := (1 + 1 / Real.log 2) / K₁ ^ 3
  have hK_pos : 0 < K := by positivity
  refine ⟨K, hK_pos, ?_⟩
  intro n hn C
  by_cases hC2 : 2 ≤ C.card
  · have hclass : (classicalExactComplexity C : ℝ) ≤
        Real.log (C.card : ℝ) / gammaParam C + 1 :=
      SolServedioCube.classicalExactComplexity_le_log_div_gamma hC2
    have hγ_pos : 0 < gammaParam C := SolServedioCube.gammaParam_pos hC2
    have hγ_le_one : gammaParam C ≤ 1 := SolServedioCube.gammaParam_le_one hC2
    have hlogC_ge : Real.log 2 ≤ Real.log (C.card : ℝ) := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast hC2
    have hlog_pos : 0 < Real.log (C.card : ℝ) := lt_of_lt_of_le hlog2_pos hlogC_ge
    have hratio_ge : Real.log 2 ≤ Real.log (C.card : ℝ) / gammaParam C := by
      calc Real.log 2
          = Real.log 2 / 1 := by ring
        _ ≤ Real.log (C.card : ℝ) / 1 := by linarith
        _ ≤ Real.log (C.card : ℝ) / gammaParam C :=
            div_le_div_of_nonneg_left (le_of_lt hlog_pos) hγ_pos hγ_le_one
    have hclass' : (classicalExactComplexity C : ℝ) ≤
        (1 + 1 / Real.log 2) * (Real.log (C.card : ℝ) / gammaParam C) := by
      have h1 : (1 : ℝ) ≤ (1 / Real.log 2) * (Real.log (C.card : ℝ) / gammaParam C) := by
        rw [one_div_mul_eq_div]
        exact (one_le_div hlog2_pos).mpr hratio_ge
      linarith
    have hne := SolServedioCube.quantumExactComplexity_nonempty C
    obtain ⟨w, A, out, hLearn⟩ := Nat.sInf_mem hne
    set Q : ℕ := quantumExactComplexity C
    have hlow := hSG n hn C hC2 (Fin w) Q A out hLearn
    have hlow1 : K₁ * (1 / Real.sqrt (gammaParam C)) ≤ (Q : ℝ) := by
      calc K₁ * (1 / Real.sqrt (gammaParam C))
          ≤ K₁ * max (1 / Real.sqrt (gammaParam C)) (Real.log (C.card : ℝ) / (n : ℝ)) :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) (le_of_lt hK₁_pos)
        _ ≤ (Q : ℝ) := hlow
    have hlow2 : K₁ * (Real.log (C.card : ℝ) / (n : ℝ)) ≤ (Q : ℝ) := by
      calc K₁ * (Real.log (C.card : ℝ) / (n : ℝ))
          ≤ K₁ * max (1 / Real.sqrt (gammaParam C)) (Real.log (C.card : ℝ) / (n : ℝ)) :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) (le_of_lt hK₁_pos)
        _ ≤ (Q : ℝ) := hlow
    have hsqrt_le : 1 / Real.sqrt (gammaParam C) ≤ (Q : ℝ) / K₁ := by
      rw [le_div_iff₀ hK₁_pos]
      linarith
    have hsqrt_nonneg : 0 ≤ 1 / Real.sqrt (gammaParam C) := by positivity
    have hsq_le : (1 / Real.sqrt (gammaParam C)) ^ 2 ≤ ((Q : ℝ) / K₁) ^ 2 :=
      pow_le_pow_left₀ hsqrt_nonneg hsqrt_le 2
    have hsq_eq : (1 / Real.sqrt (gammaParam C)) ^ 2 = 1 / gammaParam C := by
      rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hγ_pos)]
    rw [hsq_eq] at hsq_le
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hlog_le : Real.log (C.card : ℝ) ≤ (n : ℝ) * ((Q : ℝ) / K₁) := by
      have hdiv : Real.log (C.card : ℝ) / (n : ℝ) ≤ (Q : ℝ) / K₁ := by
        rw [le_div_iff₀ hK₁_pos]
        linarith
      have hmul := (div_le_iff₀ hn_pos).mp hdiv
      linarith
    have hprod_le : Real.log (C.card : ℝ) / gammaParam C ≤
        (n : ℝ) * ((Q : ℝ) / K₁) ^ 3 := by
      calc Real.log (C.card : ℝ) / gammaParam C
          = Real.log (C.card : ℝ) * (1 / gammaParam C) := by ring
        _ ≤ ((n : ℝ) * ((Q : ℝ) / K₁)) * ((Q : ℝ) / K₁) ^ 2 :=
            mul_le_mul hlog_le hsq_le (by positivity) (by positivity)
        _ = (n : ℝ) * ((Q : ℝ) / K₁) ^ 3 := by ring
    calc (classicalExactComplexity C : ℝ)
        ≤ (1 + 1 / Real.log 2) * (Real.log (C.card : ℝ) / gammaParam C) := hclass'
      _ ≤ (1 + 1 / Real.log 2) * ((n : ℝ) * ((Q : ℝ) / K₁) ^ 3) :=
          mul_le_mul_of_nonneg_left hprod_le (by positivity)
      _ = K * (n : ℝ) * (Q : ℝ) ^ 3 := by
          dsimp [K]
          ring
  · have hC1 : C.card ≤ 1 := by omega
    rw [SolServedioCube.classicalExactComplexity_eq_zero_of_card_le_one hC1, Nat.cast_zero]
    positivity
