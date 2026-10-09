-- Prove2me | solution 1 for RobustUncLP.Ellipsoidal.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T17:46:06.515791+00:00
-- url     : https://prove2.me/submissions/bffee752-a61e-4f79-9668-b02f7fa17a6a

import Mathlib
import Definitions.Def_RobustUncLP_Ellipsoidal_Setting
import Definitions.Def_RobustUncLP_Ellipsoidal_SystemC

set_option autoImplicit false

namespace P2737

open Matrix RobustUncLP.Ellipsoidal

lemma en_eq_norm {M : ℕ} (v : Fin M → ℝ) :
    euclidNorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin M))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [euclidNorm, Real.norm_eq_abs, sq_abs]

lemma en_nonneg {M : ℕ} (v : Fin M → ℝ) : 0 ≤ euclidNorm v := Real.sqrt_nonneg _

lemma en_zero {M : ℕ} : euclidNorm (0 : Fin M → ℝ) = 0 := by simp [euclidNorm]

lemma en_add {M : ℕ} (v w : Fin M → ℝ) : euclidNorm (v + w) ≤ euclidNorm v + euclidNorm w := by
  rw [en_eq_norm, en_eq_norm, en_eq_norm, WithLp.toLp_add]; exact norm_add_le _ _

lemma en_smul {M : ℕ} (c : ℝ) (v : Fin M → ℝ) : euclidNorm (c • v) = |c| * euclidNorm v := by
  rw [en_eq_norm, en_eq_norm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

lemma en_neg {M : ℕ} (v : Fin M → ℝ) : euclidNorm (-v) = euclidNorm v := by
  rw [en_eq_norm, en_eq_norm, WithLp.toLp_neg, norm_neg]

lemma dot_le_en {M : ℕ} (v w : Fin M → ℝ) : v ⬝ᵥ w ≤ euclidNorm v * euclidNorm w := by
  simpa [dotProduct, euclidNorm] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ v w

lemma en_sq {M : ℕ} (v : Fin M → ℝ) : euclidNorm v ^ 2 = v ⬝ᵥ v := by
  unfold euclidNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  simp [dotProduct, sq]

lemma en_continuous {M : ℕ} : Continuous (fun v : Fin M → ℝ => euclidNorm v) := by
  unfold euclidNorm
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun j _ => (continuous_apply j).pow 2)

lemma abs_le_en {M : ℕ} (v : Fin M → ℝ) (j : Fin M) : |v j| ≤ euclidNorm v := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => v j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ j))

/-- One block: a linear form bounded below by `-α ‖Q·‖` is `Qᵀ μ` with `‖μ‖ ≤ α`. -/
lemma block_dual {M L : ℕ} (Q : Matrix (Fin M) (Fin L) ℝ) (w : Fin L → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (h : ∀ v, 0 ≤ w ⬝ᵥ v + α * euclidNorm (Q *ᵥ v)) :
    ∃ μ, euclidNorm μ ≤ α ∧ Qᵀ *ᵥ μ = w := by
  by_contra hne
  set ball : Set (Fin M → ℝ) := {μ | euclidNorm μ ≤ α} with hball
  set S : Set (Fin L → ℝ) := (Qᵀ.mulVecLin) '' ball with hS
  have hbconv : Convex ℝ ball := by
    intro p hp q hq a b ha hb hab
    simp only [hball, Set.mem_setOf_eq] at *
    calc euclidNorm (a • p + b • q) ≤ euclidNorm (a • p) + euclidNorm (b • q) := en_add _ _
      _ = a * euclidNorm p + b * euclidNorm q := by
          rw [en_smul, en_smul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * α + b * α := by gcongr
      _ = α := by rw [← add_mul, hab, one_mul]
  have hbcpt : IsCompact ball := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_le en_continuous continuous_const) ?_
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨α, fun μ hμ => ?_⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hα]
    intro j
    rw [Real.norm_eq_abs]
    exact (abs_le_en μ j).trans hμ
  have hSconv : Convex ℝ S := hbconv.linear_image _
  have hScl : IsClosed S :=
    (hbcpt.image (LinearMap.continuous_of_finiteDimensional _)).isClosed
  have hwS : w ∉ S := by
    rintro ⟨μ, hμ, he⟩
    rw [Matrix.mulVecLin_apply] at he
    exact hne ⟨μ, hμ, he⟩
  obtain ⟨f, s, hfS, hsw⟩ := geometric_hahn_banach_closed_point hSconv hScl hwS
  set z : Fin L → ℝ := fun j => f (fun j' => if j = j' then 1 else 0) with hz
  have hfrep : ∀ v, f v = v ⬝ᵥ z := by
    intro v
    have := LinearMap.pi_apply_eq_sum_univ (f : (Fin L → ℝ) →ₗ[ℝ] ℝ) v
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this]; rfl
  -- the hypothesis at `-z`
  have h1 := h (-z)
  rw [dotProduct_neg, Matrix.mulVec_neg, en_neg] at h1
  -- a point of the ball attaining `α ‖Qz‖`
  set q := Q *ᵥ z with hq
  obtain ⟨μ, hμb, hμv⟩ : ∃ μ, euclidNorm μ ≤ α ∧ μ ⬝ᵥ q = α * euclidNorm q := by
    by_cases hq0 : euclidNorm q = 0
    · exact ⟨0, by rw [en_zero]; exact hα, by simp [hq0]⟩
    · refine ⟨(α / euclidNorm q) • q, ?_, ?_⟩
      · rw [en_smul, abs_of_nonneg (div_nonneg hα (en_nonneg q)), div_mul_cancel₀ _ hq0]
      · rw [smul_dotProduct, smul_eq_mul, ← en_sq]
        field_simp
  have h2 := hfS _ ⟨μ, hμb, rfl⟩
  rw [hfrep] at h2 hsw
  have e : (Qᵀ.mulVecLin μ) ⬝ᵥ z = μ ⬝ᵥ q := by
    rw [Matrix.mulVecLin_apply, dotProduct_comm, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose, dotProduct_comm]
  rw [e, hμv] at h2
  linarith

/-- All blocks at once. -/
lemma blocks_dual {ι : Type*} [Fintype ι] [DecidableEq ι] {L M : ι → ℕ}
    (Q : (j : ι) → Matrix (Fin (M j)) (Fin (L j)) ℝ) (W : (j : ι) → Fin (L j) → ℝ)
    (α : ι → ℝ) (hα : ∀ j, 0 ≤ α j) (C : ℝ)
    (h : ∀ u : (j : ι) → Fin (L j) → ℝ,
      0 ≤ C + ∑ j, (W j ⬝ᵥ u j + α j * euclidNorm (Q j *ᵥ u j))) :
    0 ≤ C ∧ ∀ j, ∃ μ, euclidNorm μ ≤ α j ∧ (Q j)ᵀ *ᵥ μ = W j := by
  have hC : 0 ≤ C := by simpa [en_zero] using h 0
  refine ⟨hC, fun j => block_dual (Q j) (W j) (α j) (hα j) ?_⟩
  intro v
  by_contra hneg
  rw [not_le] at hneg
  set e := W j ⬝ᵥ v + α j * euclidNorm (Q j *ᵥ v) with he
  set t := (C + 1) / (-e) with ht
  have htpos : 0 < t := div_pos (by linarith) (by linarith)
  have h1 := h (Pi.single (M := fun j => Fin (L j) → ℝ) j (t • v))
  rw [Finset.sum_eq_single j (fun b _ hb => by
      simp [Pi.single_eq_of_ne hb, en_zero]) (by simp)] at h1
  simp only [Pi.single_eq_same, dotProduct_smul, Matrix.mulVec_smul, en_smul,
    abs_of_pos htpos, smul_eq_mul] at h1
  have hte : t * e = -(C + 1) := by
    rw [ht, div_mul_eq_mul_div, div_eq_iff (neg_ne_zero.mpr hneg.ne)]; ring
  have : t * (W j ⬝ᵥ v) + α j * (t * euclidNorm (Q j *ᵥ v)) = t * e := by rw [he]; ring
  linarith

lemma convex_neg_set {E : Type*} [AddCommGroup E] [Module ℝ E] (φ : E → ℝ)
    (hφ : ∀ p q : E, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      φ (a • p + b • q) ≤ a * φ p + b * φ q) :
    Convex ℝ {p | φ p < 0} := by
  intro p hp q hq a b ha hb hab
  simp only [Set.mem_setOf_eq] at *
  have h1 := hφ p q a b ha hb hab
  rcases ha.eq_or_lt with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1; simpa using hq
  · have : a * φ p < 0 := mul_neg_of_pos_of_neg ha' hp
    have : b * φ q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hq.le
    linarith

/-- Lagrange multipliers under a Slater point, with linear equality constraints `T w = 0`. -/
theorem lagrange {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype ι] [DecidableEq ι]
    (T : V →ₗ[ℝ] W) (g : V → ℝ) (h : ι → V → ℝ)
    (hgc : ∀ p q : V, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      g (a • p + b • q) ≤ a * g p + b * g q)
    (hhc : ∀ j, ∀ p q : V, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      h j (a • p + b • q) ≤ a * h j p + b * h j q)
    (hgk : Continuous g) (hhk : ∀ j, Continuous (h j))
    (u0 : V) (hs : ∀ j, h j u0 < 0)
    (hfeas : ∀ w, T w = 0 → (∀ j, h j (u0 + w) ≤ 0) → 0 ≤ g (u0 + w)) :
    ∃ (φ : W →ₗ[ℝ] ℝ) (α : ι → ℝ), (∀ j, 0 ≤ α j) ∧
      ∀ w, 0 ≤ g (u0 + w) + φ (T w) + ∑ j, α j * h j (u0 + w) := by
  set R := LinearMap.range T with hR
  set T' : V →ₗ[ℝ] R := T.rangeRestrict with hT'def
  have hT' : Function.Surjective T' := LinearMap.surjective_rangeRestrict T
  set Lm : V × (ι → ℝ) × ℝ →ₗ[ℝ] R × (ι → ℝ) × ℝ := T'.prodMap LinearMap.id with hLm
  have hL : Function.Surjective Lm := by
    rintro ⟨r, z⟩
    obtain ⟨v, hv⟩ := hT' r
    exact ⟨(v, z), by simp [hLm, hv]⟩
  have hLapp : ∀ p : V × (ι → ℝ) × ℝ, Lm p = (T' p.1, p.2) := fun p => rfl
  have aff : ∀ p q : V, ∀ a b : ℝ, a + b = 1 →
      u0 + (a • p + b • q) = a • (u0 + p) + b • (u0 + q) := by
    intro p q a b hab
    have : u0 = a • u0 + b • u0 := by rw [← add_smul, hab, one_smul]
    rw [smul_add, smul_add]
    nth_rewrite 1 [this]
    abel
  set A' : Set (V × (ι → ℝ) × ℝ) :=
    (⋂ j, {p | h j (u0 + p.1) - p.2.1 j < 0}) ∩ {p | g (u0 + p.1) - p.2.2 < 0} with hA'
  have hA'open : IsOpen A' := by
    refine IsOpen.inter (isOpen_iInter_of_finite fun j => ?_) ?_
    · exact isOpen_lt (((hhk j).comp (continuous_const.add continuous_fst)).sub
        ((continuous_apply j).comp (continuous_fst.comp continuous_snd))) continuous_const
    · exact isOpen_lt ((hgk.comp (continuous_const.add continuous_fst)).sub
        (continuous_snd.comp continuous_snd)) continuous_const
  have hA'conv : Convex ℝ A' := by
    refine Convex.inter (convex_iInter fun j => convex_neg_set _ ?_) (convex_neg_set _ ?_)
    · intro p q a b ha hb hab
      have h1 := hhc j (u0 + p.1) (u0 + q.1) a b ha hb hab
      simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [aff p.1 q.1 a b hab]
      linear_combination h1
    · intro p q a b ha hb hab
      have h1 := hgc (u0 + p.1) (u0 + q.1) a b ha hb hab
      simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      rw [aff p.1 q.1 a b hab]
      linear_combination h1
  set B : Set (R × (ι → ℝ) × ℝ) := {y | y.1 = 0 ∧ (∀ j, y.2.1 j ≤ 0) ∧ y.2.2 ≤ 0} with hB
  have hBconv : Convex ℝ B := by
    intro y hy z hz a b ha hb hab
    obtain ⟨hy1, hy2, hy3⟩ := hy
    obtain ⟨hz1, hz2, hz3⟩ := hz
    refine ⟨by simp [hy1, hz1], fun j => ?_, ?_⟩
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos ha (hy2 j), mul_nonpos_of_nonneg_of_nonpos hb (hz2 j)]
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos ha hy3, mul_nonpos_of_nonneg_of_nonpos hb hz3]
  have hdisj : Disjoint (Lm '' A') B := by
    rw [Set.disjoint_left]
    rintro y ⟨p, hp, rfl⟩ ⟨h1, h2, h3⟩
    rw [hLapp] at h1 h2 h3
    have hTp : T p.1 = 0 := congrArg Subtype.val h1
    obtain ⟨hpA, hpg⟩ := hp
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hpA hpg
    have := hfeas p.1 hTp (fun j => by linarith [hpA j, h2 j])
    simp only at h3
    linarith
  obtain ⟨f, s, hfA, hfB⟩ := geometric_hahn_banach_open (hA'conv.linear_image Lm)
    (LinearMap.isOpenMap_of_finiteDimensional Lm hL A' hA'open) hBconv hdisj
  set e : ι → (ι → ℝ) := fun j => fun j' => if j = j' then 1 else 0 with he
  set α : ι → ℝ := fun j => -f ((0 : R), e j, (0 : ℝ)) with hα
  set β : ℝ := -f ((0 : R), (0 : ι → ℝ), (1 : ℝ)) with hβ
  set φR : R →ₗ[ℝ] ℝ := (f : R × (ι → ℝ) × ℝ →ₗ[ℝ] ℝ).comp (LinearMap.inl ℝ R ((ι → ℝ) × ℝ))
    with hφR
  have hdec : ∀ (r : R) (a : ι → ℝ) (b : ℝ), f (r, a, b) = φR r - ∑ j, α j * a j - β * b := by
    intro r a b
    have h1 : ((r, a, b) : R × (ι → ℝ) × ℝ) =
        (r, (0 : ι → ℝ), (0 : ℝ)) + (((0 : R), a, (0 : ℝ)) + ((0 : R), (0 : ι → ℝ), b)) := by
      refine Prod.ext (by simp) (Prod.ext (by simp) (by simp))
    have h2 : f ((0 : R), a, (0 : ℝ)) = ∑ j, a j * f ((0 : R), e j, (0 : ℝ)) := by
      have := LinearMap.pi_apply_eq_sum_univ ((f : R × (ι → ℝ) × ℝ →ₗ[ℝ] ℝ).comp
        ((LinearMap.inr ℝ R ((ι → ℝ) × ℝ)).comp (LinearMap.inl ℝ (ι → ℝ) ℝ))) a
      simpa [he, smul_eq_mul] using this
    have h3 : f ((0 : R), (0 : ι → ℝ), b) = b * f ((0 : R), (0 : ι → ℝ), (1 : ℝ)) := by
      have : ((0 : R), (0 : ι → ℝ), b) = b • ((0 : R), (0 : ι → ℝ), (1 : ℝ)) := by
        refine Prod.ext (by simp) (Prod.ext (by simp) (by simp))
      rw [this, map_smul, smul_eq_mul]
    rw [h1, map_add, map_add, h2, h3]
    have h4 : ∑ j, α j * a j = -∑ j, a j * f ((0 : R), e j, (0 : ℝ)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [hα]; ring
    rw [h4, hβ, hφR]
    simp only [LinearMap.comp_apply, LinearMap.inl_apply, ContinuousLinearMap.coe_coe,
      Prod.mk_zero_zero]
    ring
  have hs0 : s ≤ 0 := by
    have := hfB 0 ⟨rfl, fun j => le_rfl, le_rfl⟩
    simpa using this
  have hBnn : ∀ y ∈ B, 0 ≤ f y := by
    intro y hy
    by_contra hneg
    rw [not_le] at hneg
    have ht : 0 < (s - 1) / f y := div_pos_of_neg_of_neg (by linarith) hneg
    have hyB : ((s - 1) / f y) • y ∈ B := by
      obtain ⟨h1, h2, h3⟩ := hy
      refine ⟨by simp [h1], fun j => ?_, ?_⟩
      · simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
        exact mul_nonpos_of_nonneg_of_nonpos ht.le (h2 j)
      · simp only [Prod.smul_snd, smul_eq_mul]
        exact mul_nonpos_of_nonneg_of_nonpos ht.le h3
    have := hfB _ hyB
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at this
    linarith
  have hα0 : ∀ j, 0 ≤ α j := by
    intro j
    have hmem : ((0 : R), -e j, (0 : ℝ)) ∈ B := by
      refine ⟨rfl, fun j' => ?_, le_rfl⟩
      simp only [he, Pi.neg_apply]
      split_ifs <;> norm_num
    have := hBnn _ hmem
    have h' : ((0 : R), -e j, (0 : ℝ)) = -((0 : R), e j, (0 : ℝ)) := by
      refine Prod.ext (by simp) (Prod.ext (by simp) (by simp))
    rw [h', map_neg] at this
    simpa [hα] using this
  have hβ0 : 0 ≤ β := by
    have hmem : ((0 : R), (0 : ι → ℝ), (-1 : ℝ)) ∈ B := ⟨rfl, fun j => le_rfl, by norm_num⟩
    have := hBnn _ hmem
    have h' : ((0 : R), (0 : ι → ℝ), (-1 : ℝ)) = -((0 : R), (0 : ι → ℝ), (1 : ℝ)) := by
      refine Prod.ext (by simp) (Prod.ext (by simp) (by simp))
    rw [h', map_neg] at this
    simpa [hβ] using this
  have hβpos : 0 < β := by
    rcases hβ0.eq_or_lt with h0 | h0
    · exfalso
      set a0 : ι → ℝ := fun j => h j u0 / 2 with ha0
      have hpA : ((0 : V), a0, g u0 + 1) ∈ A' := by
        refine ⟨Set.mem_iInter.2 fun j => ?_, ?_⟩
        · show h j (u0 + 0) - a0 j < 0
          simp only [add_zero, ha0]
          linarith [hs j]
        · show g (u0 + 0) - (g u0 + 1) < 0
          simp
      have h1 := hfA _ ⟨_, hpA, rfl⟩
      have hmB : ((0 : R), a0, (0 : ℝ)) ∈ B :=
        ⟨rfl, fun j => by simp only [ha0]; linarith [hs j], le_rfl⟩
      have h2 := hfB _ hmB
      rw [hLapp] at h1
      have hT0 : T' (0 : V) = 0 := map_zero T'
      simp only [hT0] at h1
      rw [hdec] at h1 h2
      rw [← h0] at h1 h2
      simp only [map_zero] at h1 h2
      linarith
    · exact h0
  have hS : 0 < ∑ j, α j + β := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hα0 j)
    linarith
  have hmain : ∀ w : V, 0 ≤ β * g (u0 + w) + ∑ j, α j * h j (u0 + w) - φR (T' w) := by
    intro w
    have hδ : ∀ δ : ℝ, 0 < δ →
        φR (T' w) - ∑ j, α j * h j (u0 + w) - β * g (u0 + w) < δ * (∑ j, α j + β) := by
      intro δ hδ
      have hpA : (w, (fun j => h j (u0 + w) + δ), g (u0 + w) + δ) ∈ A' := by
        refine ⟨Set.mem_iInter.2 fun j => ?_, ?_⟩
        · show h j (u0 + w) - (h j (u0 + w) + δ) < 0
          linarith
        · show g (u0 + w) - (g (u0 + w) + δ) < 0
          linarith
      have h1 := hfA _ ⟨_, hpA, rfl⟩
      rw [hLapp] at h1
      simp only at h1
      rw [hdec] at h1
      have e1 : ∑ j, α j * (h j (u0 + w) + δ) = ∑ j, α j * h j (u0 + w) + (∑ j, α j) * δ := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [e1] at h1
      nlinarith
    by_contra hneg
    rw [not_le] at hneg
    have := hδ ((φR (T' w) - ∑ j, α j * h j (u0 + w) - β * g (u0 + w)) / (∑ j, α j + β))
      (div_pos (by linarith) hS)
    rw [div_mul_cancel₀ _ hS.ne'] at this
    linarith
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend φR
  have hψT : ∀ w, φR (T' w) = ψ (T w) := by
    intro w
    rw [← hψ]
    rfl
  refine ⟨(-(1 / β)) • ψ, fun j => α j / β, fun j => div_nonneg (hα0 j) hβ0, fun w => ?_⟩
  have hm := hmain w
  rw [hψT] at hm
  simp only [LinearMap.smul_apply, smul_eq_mul]
  have e2 : ∑ j, α j / β * h j (u0 + w) = (∑ j, α j * h j (u0 + w)) / β := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e2]
  have e3 : g (u0 + w) + -(1 / β) * ψ (T w) + (∑ j, α j * h j (u0 + w)) / β =
      (β * g (u0 + w) + ∑ j, α j * h j (u0 + w) - ψ (T w)) / β := by
    field_simp
    ring
  rw [e3]
  exact div_nonneg hm hβ0

section Spec

open EllipsoidalData

variable {m n k : ℕ}

lemma Pi_apply' (D : EllipsoidalData m n k) (ℓ : Fin (k + 1)) (v : Fin (D.L ℓ) → ℝ)
    (a : Fin m) (b : Fin n) :
    D.Pi ℓ v a b = D.P0 ℓ a b + ∑ j, v j * D.P ℓ j a b := by
  simp [EllipsoidalData.Pi, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply]

lemma frob_add (Λ X Y : Matrix (Fin m) (Fin n) ℝ) : frob Λ (X + Y) = frob Λ X + frob Λ Y := by
  simp [frob, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

lemma frob_sub (Λ X Y : Matrix (Fin m) (Fin n) ℝ) : frob Λ (X - Y) = frob Λ X - frob Λ Y := by
  simp [frob, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma frob_smul (Λ X : Matrix (Fin m) (Fin n) ℝ) (c : ℝ) : frob Λ (c • X) = c * frob Λ X := by
  simp only [frob, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

lemma frob_sum {L : ℕ} (Λ : Matrix (Fin m) (Fin n) ℝ) (Y : Fin L → Matrix (Fin m) (Fin n) ℝ) :
    frob Λ (∑ j, Y j) = ∑ j, frob Λ (Y j) := by
  simp only [frob, Matrix.sum_apply, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

lemma frob_zero (Λ : Matrix (Fin m) (Fin n) ℝ) : frob Λ 0 = 0 := by simp [frob]

lemma frob_Pi (D : EllipsoidalData m n k) (Λ : Matrix (Fin m) (Fin n) ℝ) (ℓ : Fin (k + 1))
    (v : Fin (D.L ℓ) → ℝ) :
    frob Λ (D.Pi ℓ v) = frob Λ (D.P0 ℓ) + ∑ j, v j * frob Λ (D.P ℓ j) := by
  rw [EllipsoidalData.Pi, frob_add, frob_sum]
  simp only [frob_smul]

lemma g_Pi (D : EllipsoidalData m n k) (x : Fin n → ℝ) (i : Fin m) (v : Fin (D.L 0) → ℝ) :
    (D.Pi 0 v *ᵥ x) i = (D.P0 0 *ᵥ x) i + ∑ j, v j * (D.P 0 j *ᵥ x) i := by
  rw [EllipsoidalData.Pi, Matrix.add_mulVec, Pi.add_apply]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring

/-- The Lagrangian identity behind `(𝒞_i)`. -/
lemma lag_id (D : EllipsoidalData m n k) (x : Fin n → ℝ) (i : Fin m)
    (Λ : Fin k → Matrix (Fin m) (Fin n) ℝ) (u : (ℓ : Fin (k + 1)) → Fin (D.L ℓ) → ℝ) :
    (D.Pi 0 (u 0) *ᵥ x) i =
      ((D.P0 0 *ᵥ x) i + ∑ ℓ' : Fin k, frob (Λ ℓ') (D.P0 0 - D.P0 ℓ'.succ))
      + ∑ ℓ' : Fin k, frob (Λ ℓ') (D.Pi ℓ'.succ (u ℓ'.succ) - D.Pi 0 (u 0))
      + ∑ j, ((D.P 0 j *ᵥ x) i + ∑ ℓ' : Fin k, frob (Λ ℓ') (D.P 0 j)) * u 0 j
      + ∑ ℓ' : Fin k, ∑ j, (-frob (Λ ℓ') (D.P ℓ'.succ j)) * u ℓ'.succ j := by
  have s1 : ∑ ℓ' : Fin k, frob (Λ ℓ') (D.Pi ℓ'.succ (u ℓ'.succ) - D.Pi 0 (u 0)) =
      ∑ ℓ' : Fin k, (frob (Λ ℓ') (D.P0 ℓ'.succ) - frob (Λ ℓ') (D.P0 0))
      + ∑ ℓ' : Fin k, ∑ j, u ℓ'.succ j * frob (Λ ℓ') (D.P ℓ'.succ j)
      - ∑ ℓ' : Fin k, ∑ j, u 0 j * frob (Λ ℓ') (D.P 0 j) := by
    simp only [frob_sub, frob_Pi, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  have s2 : ∑ j, ((D.P 0 j *ᵥ x) i + ∑ ℓ' : Fin k, frob (Λ ℓ') (D.P 0 j)) * u 0 j =
      ∑ j, u 0 j * (D.P 0 j *ᵥ x) i + ∑ ℓ' : Fin k, ∑ j, u 0 j * frob (Λ ℓ') (D.P 0 j) := by
    rw [Finset.sum_comm (f := fun ℓ' j => u 0 j * frob (Λ ℓ') (D.P 0 j)),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum]
    ring
  have s3 : ∑ ℓ' : Fin k, ∑ j, (-frob (Λ ℓ') (D.P ℓ'.succ j)) * u ℓ'.succ j =
      -∑ ℓ' : Fin k, ∑ j, u ℓ'.succ j * frob (Λ ℓ') (D.P ℓ'.succ j) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ℓ' _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have s4 : ∑ ℓ' : Fin k, frob (Λ ℓ') (D.P0 0 - D.P0 ℓ'.succ) =
      -∑ ℓ' : Fin k, (frob (Λ ℓ') (D.P0 ℓ'.succ) - frob (Λ ℓ') (D.P0 0)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun ℓ' _ => by rw [frob_sub]; ring
  rw [s1, s2, s3, s4, g_Pi]
  ring

/-- The linear part of the equality constraints `Π_{ℓ'+1}(u^{ℓ'+1}) = Π_0(u⁰)`, flattened. -/
def Tlin (D : EllipsoidalData m n k) :
    ((ℓ : Fin (k + 1)) → Fin (D.L ℓ) → ℝ) →ₗ[ℝ] (Fin k × Fin m × Fin n → ℝ) where
  toFun u p := ∑ j, u p.1.succ j * D.P p.1.succ j p.2.1 p.2.2 -
    ∑ j, u 0 j * D.P 0 j p.2.1 p.2.2
  map_add' u v := by
    ext p
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' c u := by
    ext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sub, Finset.mul_sum, mul_assoc]

lemma backward (D : EllipsoidalData m n k) (x : Fin n → ℝ) (i : Fin m)
    (Λ : Fin k → Matrix (Fin m) (Fin n) ℝ) (μ : (ℓ : Fin (k + 1)) → Fin (D.M ℓ) → ℝ)
    (ν : Fin (k + 1) → ℝ) (hS : SystemC D x i Λ μ ν) :
    ∀ u ∈ PFeas D, 0 ≤ (D.Pi 0 (u 0) *ᵥ x) i := by
  intro u hu
  obtain ⟨h1, h2, h3, h4⟩ := hS
  rw [lag_id D x i Λ u]
  have hE : ∑ ℓ' : Fin k, frob (Λ ℓ') (D.Pi ℓ'.succ (u ℓ'.succ) - D.Pi 0 (u 0)) = 0 :=
    Finset.sum_eq_zero fun ℓ' _ => by rw [hu.1 ℓ'.succ, sub_self, frob_zero]
  have hW0 : ∀ j, (D.P 0 j *ᵥ x) i + ∑ ℓ' : Fin k, frob (Λ ℓ') (D.P 0 j) =
      ((D.Q 0)ᵀ *ᵥ μ 0) j := fun j => by linarith [h2 j]
  have hWs : ∀ (ℓ' : Fin k) j, -frob (Λ ℓ') (D.P ℓ'.succ j) =
      ((D.Q ℓ'.succ)ᵀ *ᵥ μ ℓ'.succ) j := fun ℓ' j => by linarith [h3 ℓ' j]
  simp only [hW0, hWs, hE]
  have key : ∀ ℓ, -ν ℓ ≤ ∑ j, ((D.Q ℓ)ᵀ *ᵥ μ ℓ) j * u ℓ j := by
    intro ℓ
    have e : ∑ j, ((D.Q ℓ)ᵀ *ᵥ μ ℓ) j * u ℓ j = μ ℓ ⬝ᵥ (D.Q ℓ *ᵥ u ℓ) := by
      change ((D.Q ℓ)ᵀ *ᵥ μ ℓ) ⬝ᵥ u ℓ = _
      rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
    rw [e]
    have hc := dot_le_en (-μ ℓ) (D.Q ℓ *ᵥ u ℓ)
    rw [en_neg, neg_dotProduct] at hc
    have hq := hu.2 ℓ
    have hm := h4 ℓ
    have := mul_le_of_le_one_right (en_nonneg (μ ℓ)) hq
    linarith
  have hsum : -(∑ ℓ, ν ℓ) ≤ ∑ ℓ, ∑ j, ((D.Q ℓ)ᵀ *ᵥ μ ℓ) j * u ℓ j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun ℓ _ => key ℓ
  simp only [Fin.sum_univ_succ] at hsum h1
  linarith

lemma forward (D : EllipsoidalData m n k) (x : Fin n → ℝ) (i : Fin m) (hC : D.SlaterC)
    (hnn : ∀ u ∈ PFeas D, 0 ≤ (D.Pi 0 (u 0) *ᵥ x) i) :
    ∃ (Λ : Fin k → Matrix (Fin m) (Fin n) ℝ) (μ : (ℓ : Fin (k + 1)) → Fin (D.M ℓ) → ℝ)
      (ν : Fin (k + 1) → ℝ), SystemC D x i Λ μ ν := by
  obtain ⟨A, hA⟩ := hC
  choose u0 hu0A hu0n using hA
  have hE0 : ∀ ℓ, D.Pi ℓ (u0 ℓ) = D.Pi 0 (u0 0) := fun ℓ => by rw [← hu0A ℓ, ← hu0A 0]
  have hgc : ∀ p q : ((ℓ : Fin (k + 1)) → Fin (D.L ℓ) → ℝ), ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a + b = 1 → (D.Pi 0 ((a • p + b • q) 0) *ᵥ x) i ≤
        a * (D.Pi 0 (p 0) *ᵥ x) i + b * (D.Pi 0 (q 0) *ᵥ x) i := by
    intro p q a b _ _ hab
    simp only [g_Pi, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum]
    apply le_of_eq
    linear_combination (-(D.P0 0 *ᵥ x) i) * hab
  have hhc : ∀ ℓ, ∀ p q : ((ℓ : Fin (k + 1)) → Fin (D.L ℓ) → ℝ), ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a + b = 1 → euclidNorm (D.Q ℓ *ᵥ (a • p + b • q) ℓ) - 1 ≤
        a * (euclidNorm (D.Q ℓ *ᵥ p ℓ) - 1) + b * (euclidNorm (D.Q ℓ *ᵥ q ℓ) - 1) := by
    intro ℓ p q a b ha hb hab
    simp only [Pi.add_apply, Pi.smul_apply, Matrix.mulVec_add, Matrix.mulVec_smul]
    have h1 := en_add (a • (D.Q ℓ *ᵥ p ℓ)) (b • (D.Q ℓ *ᵥ q ℓ))
    rw [en_smul, en_smul, abs_of_nonneg ha, abs_of_nonneg hb] at h1
    linear_combination h1 + hab
  have hgk : Continuous fun u : ((ℓ : Fin (k + 1)) → Fin (D.L ℓ) → ℝ) =>
      (D.Pi 0 (u 0) *ᵥ x) i := by
    simp only [g_Pi]
    fun_prop
  have hhk : ∀ ℓ, Continuous fun u : ((ℓ : Fin (k + 1)) → Fin (D.L ℓ) → ℝ) =>
      euclidNorm (D.Q ℓ *ᵥ u ℓ) - 1 := fun ℓ =>
    (en_continuous.comp (Continuous.matrix_mulVec continuous_const (continuous_apply ℓ))).sub
      continuous_const
  have hfeas : ∀ w, Tlin D w = 0 → (∀ ℓ, euclidNorm (D.Q ℓ *ᵥ (u0 + w) ℓ) - 1 ≤ 0) →
      0 ≤ (D.Pi 0 ((u0 + w) 0) *ᵥ x) i := by
    intro w hw hle
    apply hnn
    refine ⟨fun ℓ => ?_, fun ℓ => by linarith [hle ℓ]⟩
    induction ℓ using Fin.cases with
    | zero => rfl
    | succ ℓ' =>
      ext a b
      rw [Pi_apply', Pi_apply']
      have h1 := congrFun hw (ℓ', a, b)
      simp only [Tlin, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h1
      have h2 := congrArg (fun M => M a b) (hE0 ℓ'.succ)
      simp only [Pi_apply'] at h2
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      linarith
  obtain ⟨φ, α, hα, hL⟩ := lagrange (Tlin D) (fun u => (D.Pi 0 (u 0) *ᵥ x) i)
    (fun ℓ u => euclidNorm (D.Q ℓ *ᵥ u ℓ) - 1) hgc hhc hgk hhk u0
    (fun ℓ => sub_neg.mpr (hu0n ℓ)) hfeas
  set c : Fin k × Fin m × Fin n → ℝ := fun p => φ (fun p' => if p = p' then 1 else 0) with hc
  have hφ : ∀ y, φ y = ∑ p, y p * c p := by
    intro y
    rw [LinearMap.pi_apply_eq_sum_univ φ y]
    simp only [smul_eq_mul, hc]
  set Λs : Fin k → Matrix (Fin m) (Fin n) ℝ := fun ℓ' a b => -c (ℓ', a, b) with hΛs
  have hφT : ∀ u, φ (Tlin D (u - u0)) =
      -∑ ℓ' : Fin k, frob (Λs ℓ') (D.Pi ℓ'.succ (u ℓ'.succ) - D.Pi 0 (u 0)) := by
    intro u
    rw [hφ]
    simp only [Fintype.sum_prod_type, frob, hΛs, neg_mul, Finset.sum_neg_distrib, neg_neg]
    refine Finset.sum_congr rfl fun ℓ' _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    have h2 := congrArg (fun M => M a b) (hE0 ℓ'.succ)
    simp only [Pi_apply'] at h2
    simp only [Tlin, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Matrix.sub_apply, Pi_apply',
      sub_mul, Finset.sum_sub_distrib]
    linear_combination (-c (ℓ', a, b)) * h2
  set W : (ℓ : Fin (k + 1)) → Fin (D.L ℓ) → ℝ :=
    Fin.cases (motive := fun ℓ => Fin (D.L ℓ) → ℝ)
      (fun j => (D.P 0 j *ᵥ x) i + ∑ ℓ' : Fin k, frob (Λs ℓ') (D.P 0 j))
      (fun ℓ' j => -frob (Λs ℓ') (D.P ℓ'.succ j)) with hW
  set K := (D.P0 0 *ᵥ x) i + ∑ ℓ' : Fin k, frob (Λs ℓ') (D.P0 0 - D.P0 ℓ'.succ) with hK
  have hblk : ∀ u : ((ℓ : Fin (k + 1)) → Fin (D.L ℓ) → ℝ),
      0 ≤ (K - ∑ ℓ, α ℓ) + ∑ ℓ, (W ℓ ⬝ᵥ u ℓ + α ℓ * euclidNorm (D.Q ℓ *ᵥ u ℓ)) := by
    intro u
    have h1 := hL (u - u0)
    have e0 : u0 + (u - u0) = u := by abel
    rw [e0, hφT] at h1
    have h2 := lag_id D x i Λs u
    have h3 : ∑ ℓ, (W ℓ ⬝ᵥ u ℓ + α ℓ * euclidNorm (D.Q ℓ *ᵥ u ℓ)) =
        ∑ j, ((D.P 0 j *ᵥ x) i + ∑ ℓ' : Fin k, frob (Λs ℓ') (D.P 0 j)) * u 0 j
        + ∑ ℓ' : Fin k, ∑ j, (-frob (Λs ℓ') (D.P ℓ'.succ j)) * u ℓ'.succ j
        + ∑ ℓ, α ℓ * euclidNorm (D.Q ℓ *ᵥ u ℓ) := by
      rw [Finset.sum_add_distrib, Fin.sum_univ_succ (f := fun ℓ => W ℓ ⬝ᵥ u ℓ)]
      simp only [hW, Fin.cases_zero, Fin.cases_succ, dotProduct]
    have h4 : ∑ ℓ, α ℓ * (euclidNorm (D.Q ℓ *ᵥ u ℓ) - 1) =
        ∑ ℓ, α ℓ * euclidNorm (D.Q ℓ *ᵥ u ℓ) - ∑ ℓ, α ℓ := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    rw [h4] at h1
    rw [h3]
    linarith
  obtain ⟨hC0, hμ⟩ := blocks_dual D.Q W α hα (K - ∑ ℓ, α ℓ) hblk
  choose μ hμn hμQ using hμ
  refine ⟨Λs, μ, α, ?_, ?_, ?_, ?_⟩
  · linarith
  · intro j
    rw [hμQ 0]
    simp only [hW, Fin.cases_zero]
    ring
  · intro ℓ' j
    rw [hμQ ℓ'.succ]
    simp only [hW, Fin.cases_succ]
    ring
  · intro ℓ
    exact hμn ℓ

end Spec

end P2737

open RobustUncLP.Ellipsoidal Matrix RobustUncLP.Ellipsoidal.EllipsoidalData in
theorem solution {m n k : ℕ} (D : EllipsoidalData m n k) (f : Fin n → ℝ)
    (hB : UncBounded D.uncSet) (hC : D.SlaterC) :
    ∀ x : Fin n → ℝ, x ∈ RobustUncLP.WorstCase.robustFeas D.uncSet f ↔
      (f ⬝ᵥ x = 1 ∧ ∀ i : Fin m, ∃ (Λ : Fin k → Matrix (Fin m) (Fin n) ℝ)
        (μ : (ℓ : Fin (k + 1)) → Fin (D.M ℓ) → ℝ) (ν : Fin (k + 1) → ℝ), SystemC D x i Λ μ ν) := by
  intro x
  constructor
  · intro hx
    refine ⟨hx.2, fun i => P2737.forward D x i hC fun u hu => ?_⟩
    have hA : D.Pi 0 (u 0) ∈ D.uncSet := by
      simp only [EllipsoidalData.uncSet, Set.mem_iInter]
      intro ℓ
      exact ⟨u ℓ, (hu.1 ℓ).symm, hu.2 ℓ⟩
    exact hx.1 _ hA i
  · rintro ⟨hfx, hsys⟩
    refine ⟨fun A hA => ?_, hfx⟩
    simp only [EllipsoidalData.uncSet, Set.mem_iInter] at hA
    choose u hu1 hu2 using fun ℓ => hA ℓ
    have hu : u ∈ PFeas D := ⟨fun ℓ => by rw [← hu1 ℓ, ← hu1 0], hu2⟩
    intro i
    obtain ⟨Λ, μ, ν, hS⟩ := hsys i
    have := P2737.backward D x i Λ μ ν hS u hu
    rw [← hu1 0] at this
    exact this
