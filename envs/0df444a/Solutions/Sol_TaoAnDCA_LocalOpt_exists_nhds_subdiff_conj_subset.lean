-- Prove2me | solution 1 for TaoAnDCA.LocalOpt.exists_nhds_subdiff_conj_subset
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T02:42:18.488048+00:00
-- url     : https://prove2.me/submissions/870ab72a-e2ce-463b-8038-ae0bf47d83cb

import Mathlib
import Definitions.Def_TaoAnDCA_LocalOpt_Setting

open Filter Topology
open TaoAnDCA.GlobalOpt CondatPD.FinDim

namespace TaoAnDCA.LocalOpt


section Sep
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma h33_epi_closed (f : E → EReal) (hlsc : LowerSemicontinuous f) :
    IsClosed {p : E × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} := by
  have : {p : E × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} =
      (Prod.map id (fun r : ℝ => (r : EReal))) ⁻¹' {p : E × EReal | f p.1 ≤ p.2} := by
    ext p; simp
  rw [this]
  exact hlsc.isClosed_epigraph.preimage (continuous_id.prodMap continuous_coe_real_ereal)

lemma h33_minorant (f : E → EReal) (hbot : ∀ x, f x ≠ ⊥) (hne : ∃ x, f x ≠ ⊤)
    (hlsc : LowerSemicontinuous f) (hcv : Convex ℝ {p : E × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)}) :
    ∃ (l : StrongDual ℝ E) (b : ℝ), ∀ y (c : ℝ), f y = c → l y + b ≤ c := by
  set C : Set (E × ℝ) := {p | f p.1 ≤ ((p.2 : ℝ) : EReal)} with hC
  have hCc : IsClosed C := h33_epi_closed f hlsc
  have hCv : Convex ℝ C := hcv
  obtain ⟨y0, hy0⟩ := hne
  lift f y0 to ℝ using ⟨hy0, hbot y0⟩ with c0 hc0
  have hnot : (y0, c0 - 1) ∉ C := by
    simp only [hC, Set.mem_setOf_eq, ← hc0, EReal.coe_le_coe_iff, not_le]; linarith
  obtain ⟨ℓ, u, hl1, hl2⟩ := geometric_hahn_banach_point_closed hCv hCc hnot
  set φ : StrongDual ℝ E := ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ) with hφ
  set β : ℝ := ℓ (0, 1) with hβ
  have hℓ : ∀ y r, ℓ (y, r) = φ y + r * β := by
    intro y r
    have : (y, r) = ((y, 0) : E × ℝ) + r • ((0, 1) : E × ℝ) := by simp
    rw [this, map_add, map_smul, smul_eq_mul]
    rfl
  have h0 := hl2 (y0, c0) (by simp [hC, ← hc0])
  rw [hℓ] at hl1 h0
  have hβ : 0 < β := by nlinarith
  refine ⟨-(β⁻¹ • φ), u / β, fun y c hc => ?_⟩
  have := hl2 (y, c) (by simp [hC, hc])
  rw [hℓ] at this
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [div_eq_inv_mul]
  have e : β⁻¹ * β = 1 := inv_mul_cancel₀ hβ.ne'
  have hi : 0 < β⁻¹ := inv_pos.2 hβ
  have := mul_lt_mul_of_pos_left this hi
  have e2 : β⁻¹ * (φ y + c * β) = β⁻¹ * φ y + c := by field_simp
  linarith

lemma h33_sep (f : E → EReal) (hbot : ∀ x, f x ≠ ⊥) (hne : ∃ x, f x ≠ ⊤)
    (hlsc : LowerSemicontinuous f) (hcv : Convex ℝ {p : E × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)})
    (x : E) (z : ℝ) (hz : (z : EReal) < f x) :
    ∃ (l : StrongDual ℝ E) (b : ℝ), (∀ y (c : ℝ), f y = c → l y + b ≤ c) ∧ z < l x + b := by
  obtain ⟨l0, b0, hl0⟩ := h33_minorant f hbot hne hlsc hcv
  set C : Set (E × ℝ) := {p | f p.1 ≤ ((p.2 : ℝ) : EReal)} with hC
  have hCc : IsClosed C := h33_epi_closed f hlsc
  have hCv : Convex ℝ C := hcv
  have hnot : (x, z) ∉ C := by
    simp only [hC, Set.mem_setOf_eq, not_le]; exact hz
  obtain ⟨ℓ, u, hl1, hl2⟩ := geometric_hahn_banach_point_closed hCv hCc hnot
  set φ : StrongDual ℝ E := ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ) with hφ
  set β : ℝ := ℓ (0, 1) with hβ
  have hℓ : ∀ y r, ℓ (y, r) = φ y + r * β := by
    intro y r
    have : (y, r) = ((y, 0) : E × ℝ) + r • ((0, 1) : E × ℝ) := by simp
    rw [this, map_add, map_smul, smul_eq_mul]
    rfl
  rw [hℓ] at hl1
  have hC' : ∀ y (c : ℝ), f y = c → ∀ r, c ≤ r → u < φ y + r * β := by
    intro y c hc r hr
    have := hl2 (y, r) (by simp [hC, hc, hr])
    rwa [hℓ] at this
  obtain ⟨y0, hy0⟩ := hne
  lift f y0 to ℝ using ⟨hy0, hbot y0⟩ with c0 hc0
  have hβ0 : 0 ≤ β := by
    by_contra hneg
    push_neg at hneg
    set r := max c0 ((u - φ y0) / β)
    have h1 := hC' y0 c0 hc0.symm r (le_max_left _ _)
    have h2 : (u - φ y0) / β ≤ r := le_max_right _ _
    rw [div_le_iff_of_neg hneg] at h2
    linarith
  rcases eq_or_lt_of_le hβ0 with hβ0 | hβpos
  · have hβ' : β = 0 := hβ0.symm
    rw [hβ', mul_zero, add_zero] at hl1
    have hdom : ∀ y (c : ℝ), f y = c → u < φ y := by
      intro y c hc
      have := hC' y c hc c le_rfl
      rwa [hβ', mul_zero, add_zero] at this
    have hpos : 0 < u - φ x := by linarith
    set lam := max 0 ((z - l0 x - b0) / (u - φ x)) + 1 with hlam
    have hlam0 : 0 < lam := by positivity
    refine ⟨l0 - lam • φ, b0 + lam * u, fun y c hc => ?_, ?_⟩
    · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have := hl0 y c hc
      have := hdom y c hc
      nlinarith
    · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have h1 : (z - l0 x - b0) / (u - φ x) ≤ max 0 ((z - l0 x - b0) / (u - φ x)) := le_max_right _ _
      rw [div_le_iff₀ hpos] at h1
      have h2 : lam * (u - φ x) = max 0 ((z - l0 x - b0) / (u - φ x)) * (u - φ x) + (u - φ x) := by
        rw [hlam]; ring
      nlinarith
  · refine ⟨-(β⁻¹ • φ), u / β, fun y c hc => ?_, ?_⟩
    · have := hC' y c hc c le_rfl
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [div_eq_inv_mul]
      have hi : 0 < β⁻¹ := inv_pos.2 hβpos
      have := mul_lt_mul_of_pos_left this hi
      have e2 : β⁻¹ * (φ y + c * β) = β⁻¹ * φ y + c := by field_simp
      linarith
    · simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [div_eq_inv_mul]
      have hi : 0 < β⁻¹ := inv_pos.2 hβpos
      have := mul_lt_mul_of_pos_left hl1 hi
      have e2 : β⁻¹ * (φ x + z * β) = β⁻¹ * φ x + z := by field_simp
      linarith

end Sep


section Conj
variable {n : ℕ}

lemma h33_young (g : EuclideanSpace ℝ (Fin n) → EReal) (y s : EuclideanSpace ℝ (Fin n)) :
    ((inner ℝ y s : ℝ) : EReal) - g s ≤ conj g y :=
  le_iSup (fun s' => ((inner ℝ y s' : ℝ) : EReal) - g s') s

lemma h33_conj_ne_bot (g : EuclideanSpace ℝ (Fin n) → EReal) (hbot : ∀ x, g x ≠ ⊥)
    (hne : ∃ x, g x ≠ ⊤) (y : EuclideanSpace ℝ (Fin n)) : conj g y ≠ ⊥ := by
  obtain ⟨x0, hx0⟩ := hne
  intro h
  have h2 := h33_young g y x0
  rw [h] at h2
  lift g x0 to ℝ using ⟨hx0, hbot x0⟩ with c
  rw [← EReal.coe_sub] at h2
  exact EReal.coe_ne_bot _ (le_bot_iff.1 h2)

lemma h33_conj_coe (g : EuclideanSpace ℝ (Fin n) → EReal) (hbot : ∀ x, g x ≠ ⊥)
    (hne : ∃ x, g x ≠ ⊤) (y : EuclideanSpace ℝ (Fin n)) (hy : conj g y ≠ ⊤) :
    conj g y = (((conj g y).toReal : ℝ) : EReal) :=
  (EReal.coe_toReal hy (h33_conj_ne_bot g hbot hne y)).symm

lemma h33_young_real (g : EuclideanSpace ℝ (Fin n) → EReal) (y s : EuclideanSpace ℝ (Fin n))
    (c A : ℝ) (hc : g s = c) (hA : conj g y = A) : inner ℝ y s - c ≤ A := by
  have := h33_young g y s
  rw [hc, hA, ← EReal.coe_sub, EReal.coe_le_coe_iff] at this
  exact this

lemma h33_conj_le (g : EuclideanSpace ℝ (Fin n) → EReal) (hbot : ∀ x, g x ≠ ⊥)
    (y : EuclideanSpace ℝ (Fin n)) (M : ℝ)
    (h : ∀ s (c : ℝ), g s = c → inner ℝ y s - c ≤ M) : conj g y ≤ (M : EReal) := by
  apply iSup_le
  intro s
  rcases eq_or_ne (g s) ⊤ with hs | hs
  · rw [hs, EReal.sub_top]; exact bot_le
  lift g s to ℝ using ⟨hs, hbot s⟩ with c hc
  rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
  exact h s c hc.symm

lemma h33_fm (g : EuclideanSpace ℝ (Fin n) → EReal)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (x : EuclideanSpace ℝ (Fin n)) (z : ℝ) (hz : (z : EReal) < g x) :
    ∃ w, (z : EReal) < ((inner ℝ w x : ℝ) : EReal) - conj g w := by
  obtain ⟨hbot, hne, hlsc, hcv⟩ := hg
  obtain ⟨l, b, hl, hlz⟩ := h33_sep g hbot hne hlsc hcv x z hz
  set w : EuclideanSpace ℝ (Fin n) := (InnerProductSpace.toDual ℝ _).symm l with hw
  have hwl : ∀ y, inner ℝ w y = l y := by
    intro y; rw [hw]; exact InnerProductSpace.toDual_symm_apply
  refine ⟨w, ?_⟩
  have hconj : conj g w ≤ ((-b : ℝ) : EReal) := by
    apply h33_conj_le g hbot
    intro s c hc
    rw [hwl]
    have := hl s c hc
    linarith
  have h2 : ((l x + b : ℝ) : EReal) ≤ ((inner ℝ w x : ℝ) : EReal) - conj g w := by
    calc ((l x + b : ℝ) : EReal) = ((inner ℝ w x : ℝ) : EReal) - ((-b : ℝ) : EReal) := by
          rw [← EReal.coe_sub, hwl]; congr 1; ring
      _ ≤ _ := EReal.sub_le_sub le_rfl hconj
  exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hlz) h2

/-- elements of `∂g*(y)` lie in `dom g` with the Fenchel equality. -/
lemma h33_mem_dom (g : EuclideanSpace ℝ (Fin n) → EReal)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (y x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ subdiff (conj g) y) :
    ∃ c A : ℝ, g x = c ∧ conj g y = A ∧ A = inner ℝ y x - c := by
  have hbot := hg.1
  have hne := hg.2.1
  have hy : conj g y ≠ ⊤ := hx.1
  set A := (conj g y).toReal with hAdef
  have hA : conj g y = (A : EReal) := h33_conj_coe g hbot hne y hy
  have hle : g x ≤ ((inner ℝ y x - A : ℝ) : EReal) := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨w, hw⟩ := h33_fm g hg x (inner ℝ y x - A) hlt
    have hwt : conj g w ≠ ⊤ := by
      intro h; rw [h, EReal.sub_top] at hw; exact absurd hw (by simp)
    have hwb := h33_conj_ne_bot g hbot hne w
    lift conj g w to ℝ using ⟨hwt, hwb⟩ with D hD
    have h1 := hx.2 w
    rw [hA, ← hD, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    rw [← EReal.coe_sub, EReal.coe_lt_coe_iff] at hw
    rw [inner_sub_right] at h1
    linarith [real_inner_comm x w, real_inner_comm x y]
  have hxt : g x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hle
  lift g x to ℝ using ⟨hxt, hbot x⟩ with c hc
  rw [EReal.coe_le_coe_iff] at hle
  have hyoung := h33_young_real g y x c A hc.symm hA
  exact ⟨c, A, rfl, hA, by linarith⟩

end Conj

section Reg
variable {n : ℕ}

lemma h33_convexOn_ball (g : EuclideanSpace ℝ (Fin n) → EReal) (hbot : ∀ x, g x ≠ ⊥)
    (hne : ∃ x, g x ≠ ⊤) (y0 : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
    (hball : Metric.ball y0 ρ ⊆ effDom (conj g)) :
    ConvexOn ℝ (Metric.ball y0 ρ) (fun y => (conj g y).toReal) := by
  refine ⟨convex_ball _ _, ?_⟩
  intro y1 hy1 y2 hy2 a b ha hb hab
  have hy : a • y1 + b • y2 ∈ Metric.ball y0 ρ := (convex_ball y0 ρ) hy1 hy2 ha hb hab
  have h1 : conj g y1 = (((conj g y1).toReal : ℝ) : EReal) := h33_conj_coe g hbot hne y1 (hball hy1)
  have h2 : conj g y2 = (((conj g y2).toReal : ℝ) : EReal) := h33_conj_coe g hbot hne y2 (hball hy2)
  have hle : conj g (a • y1 + b • y2) ≤
      ((a * (conj g y1).toReal + b * (conj g y2).toReal : ℝ) : EReal) := by
    apply h33_conj_le g hbot
    intro s c hc
    have e1 := h33_young_real g y1 s c _ hc h1
    have e2 := h33_young_real g y2 s c _ hc h2
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have hc' : c = a * c + b * c := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left e1 ha, mul_le_mul_of_nonneg_left e2 hb]
  have h3 := h33_conj_coe g hbot hne _ (hball hy)
  rw [h3] at hle
  have := EReal.coe_le_coe_iff.1 hle
  simpa [smul_eq_mul] using this

lemma h33_cont (g : EuclideanSpace ℝ (Fin n) → EReal) (hbot : ∀ x, g x ≠ ⊥)
    (hne : ∃ x, g x ≠ ⊤) (y0 : EuclideanSpace ℝ (Fin n))
    (hy0 : y0 ∈ interior (effDom (conj g))) :
    ∃ δ > 0, Metric.ball y0 δ ⊆ effDom (conj g) ∧
      ContinuousAt (fun y => (conj g y).toReal) y0 := by
  obtain ⟨t, hts, hto, hy0t⟩ := mem_interior.1 hy0
  obtain ⟨δ, hδ, hb⟩ := Metric.isOpen_iff.1 hto y0 hy0t
  have hball : Metric.ball y0 δ ⊆ effDom (conj g) := hb.trans hts
  refine ⟨δ, hδ, hball, ?_⟩
  have hc := (h33_convexOn_ball g hbot hne y0 δ hball).continuousOn Metric.isOpen_ball
  exact hc.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))

lemma h33_bound (g : EuclideanSpace ℝ (Fin n) → EReal) (hbot : ∀ x, g x ≠ ⊥)
    (hne : ∃ x, g x ≠ ⊤) (y0 : EuclideanSpace ℝ (Fin n))
    (hy0 : y0 ∈ interior (effDom (conj g))) :
    ∃ δ > 0, Metric.ball y0 δ ⊆ effDom (conj g) ∧
      ContinuousAt (fun y => (conj g y).toReal) y0 ∧
      ∀ y' ∈ Metric.ball y0 (δ / 4), ∀ x ∈ subdiff (conj g) y', ‖x‖ ≤ 4 / δ := by
  obtain ⟨δ0, hδ0, hball0, hcont⟩ := h33_cont g hbot hne y0 hy0
  obtain ⟨δ1, hδ1, hδ1'⟩ := Metric.continuousAt_iff.1 hcont 1 one_pos
  set δ := min δ0 δ1 with hδ
  have hδpos : 0 < δ := lt_min hδ0 hδ1
  have hδ0' : δ ≤ δ0 := min_le_left _ _
  have hδ1'' : δ ≤ δ1 := min_le_right _ _
  have hball : Metric.ball y0 δ ⊆ effDom (conj g) :=
    (Metric.ball_subset_ball hδ0').trans hball0
  refine ⟨δ, hδpos, hball, hcont, ?_⟩
  intro y' hy' x hx
  by_cases hx0 : x = 0
  · rw [hx0, norm_zero]; positivity
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  set t : ℝ := δ / 2 / ‖x‖ with ht
  have htpos : 0 < t := by positivity
  set y'' := y' + t • x with hy''
  have hdist' : dist y' y0 < δ / 4 := hy'
  have hnorm : ‖t • x‖ = δ / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, ht]; field_simp
  have hy''b : y'' ∈ Metric.ball y0 δ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have : y'' - y0 = (y' - y0) + t • x := by rw [hy'']; abel
    rw [this]
    calc ‖(y' - y0) + t • x‖ ≤ ‖y' - y0‖ + ‖t • x‖ := norm_add_le _ _
      _ < δ / 4 + δ / 2 := by
          rw [hnorm]; have := (dist_eq_norm y' y0) ▸ hdist'; linarith
      _ < δ := by linarith
  have hy'b : y' ∈ Metric.ball y0 δ := by
    rw [Metric.mem_ball]; linarith
  have e1 := hδ1' (lt_of_lt_of_le (Metric.mem_ball.1 hy'b) hδ1'')
  have e2 := hδ1' (lt_of_lt_of_le (Metric.mem_ball.1 hy''b) hδ1'')
  have c1 := h33_conj_coe g hbot hne y' (hball hy'b)
  have c2 := h33_conj_coe g hbot hne y'' (hball hy''b)
  have h := hx.2 y''
  rw [c1, c2] at h
  have hin : inner ℝ x (y'' - y') = δ / 2 * ‖x‖ := by
    have : y'' - y' = t • x := by rw [hy'']; abel
    rw [this, real_inner_smul_right, real_inner_self_eq_norm_sq, ht]
    field_simp
  rw [hin, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  rw [Real.dist_eq, abs_lt] at e1 e2
  rw [le_div_iff₀ hδpos]
  nlinarith [e1.1, e1.2, e2.1, e2.2]

lemma h33_usc (g : EuclideanSpace ℝ (Fin n) → EReal)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (ys : EuclideanSpace ℝ (Fin n)) (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (h12a : ys ∈ interior (effDom (conj g))) (h12b : subdiff (conj g) ys ⊆ U) :
    ∃ V ∈ 𝓝 ys, ∀ y ∈ V, subdiff (conj g) y ⊆ U := by
  have hbot := hg.1
  have hne := hg.2.1
  obtain ⟨δ, hδ, hball, hcont, hbd⟩ := h33_bound g hbot hne ys h12a
  by_contra hno
  push_neg at hno
  have hk : ∀ k : ℕ, ∃ y, dist y ys < δ / 4 * (1 / ((k : ℝ) + 1)) ∧
      ∃ x ∈ subdiff (conj g) y, x ∉ U := by
    intro k
    have hpos : 0 < δ / 4 * (1 / ((k : ℝ) + 1)) := by positivity
    obtain ⟨y, hy, hyn⟩ := hno (Metric.ball ys (δ / 4 * (1 / ((k : ℝ) + 1))))
      (Metric.ball_mem_nhds _ hpos)
    rw [Set.not_subset] at hyn
    exact ⟨y, hy, hyn⟩
  choose y hy x hx hxU using hk
  have hyle : ∀ k, y k ∈ Metric.ball ys (δ / 4) := by
    intro k
    rw [Metric.mem_ball]
    refine lt_of_lt_of_le (hy k) ?_
    have : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith
  have hxb : ∀ k, x k ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (4 / δ) := by
    intro k
    rw [mem_closedBall_zero_iff]
    exact hbd (y k) (hyle k) (x k) (hx k)
  have hylim : Tendsto y atTop (𝓝 ys) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h0 : Tendsto (fun k : ℕ => δ / 4 * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (δ / 4)
    exact squeeze_zero (fun k => dist_nonneg) (fun k => (hy k).le) h0
  obtain ⟨xb, -, φ, hφ, hxlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_closedBall) hxb
  have hylim' : Tendsto (y ∘ φ) atTop (𝓝 ys) := hylim.comp hφ.tendsto_atTop
  have hxbU : xb ∉ U := by
    intro hxbU
    have hcl : IsClosed Uᶜ := hU.isClosed_compl
    exact (hcl.mem_of_tendsto hxlim (Eventually.of_forall (fun k => hxU (φ k)))) hxbU
  apply hxbU
  apply h12b
  show InertialFB.IFB.IsSubgradient (conj g) ys xb
  refine ⟨interior_subset h12a, ?_⟩
  intro v
  rcases eq_or_ne (conj g v) ⊤ with hv | hv
  · rw [hv]; exact le_top
  have hvc := h33_conj_coe g hbot hne v hv
  have hlim : Tendsto (fun k => (conj g (y (φ k))).toReal + inner ℝ (x (φ k)) (v - y (φ k)))
      atTop (𝓝 ((conj g ys).toReal + inner ℝ xb (v - ys))) := by
    refine Tendsto.add (hcont.tendsto.comp hylim') ?_
    exact Tendsto.inner hxlim (tendsto_const_nhds.sub hylim')
  have hle : (conj g ys).toReal + inner ℝ xb (v - ys) ≤ (conj g v).toReal := by
    refine le_of_tendsto' hlim (fun k => ?_)
    have h := (hx (φ k)).2 v
    have hyk : conj g (y (φ k)) = (((conj g (y (φ k))).toReal : ℝ) : EReal) :=
      h33_conj_coe g hbot hne _ (hball (hyle _ |> fun h => Metric.ball_subset_ball (by linarith) h))
    rw [hyk, hvc, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
    exact h
  rw [h33_conj_coe g hbot hne ys (interior_subset h12a), hvc, ← EReal.coe_add,
    EReal.coe_le_coe_iff]
  exact hle

end Reg

section Ex
variable {n : ℕ}

lemma h33_subgrad_of_min (g : EuclideanSpace ℝ (Fin n) → EReal) (hbot : ∀ x, g x ≠ ⊥)
    (y x : EuclideanSpace ℝ (Fin n)) (c : ℝ) (hc : g x = c)
    (hmin : ∀ s (c' : ℝ), g s = c' → c - inner ℝ y x ≤ c' - inner ℝ y s) :
    x ∈ subdiff (conj g) y := by
  have hconj : conj g y = ((inner ℝ y x - c : ℝ) : EReal) := by
    apply le_antisymm
    · apply h33_conj_le g hbot; intro s c' hs; have := hmin s c' hs; linarith
    · have := h33_young g y x; rwa [hc, ← EReal.coe_sub] at this
  show InertialFB.IFB.IsSubgradient (conj g) y x
  refine ⟨by rw [hconj]; exact EReal.coe_ne_top _, fun v => ?_⟩
  rw [hconj, ← EReal.coe_add]
  have := h33_young g v x
  rw [hc, ← EReal.coe_sub] at this
  refine le_trans (le_of_eq ?_) this
  congr 1
  rw [inner_sub_right]
  linarith [real_inner_comm x y, real_inner_comm x v]

lemma h33_exists_subgrad (g : EuclideanSpace ℝ (Fin n) → EReal)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ interior (effDom (conj g))) :
    ∃ x, x ∈ subdiff (conj g) y := by
  have hbot := hg.1
  have hne := hg.2.1
  obtain ⟨δ0, hδ0, hball0, hcont⟩ := h33_cont g hbot hne y hy
  obtain ⟨ρ1, hρ1, hρ1'⟩ := Metric.continuousAt_iff.1 hcont 1 one_pos
  obtain ⟨ρ, hρ, hρ0, hρ1''⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ δ0 ∧ ρ ≤ ρ1 :=
    ⟨min δ0 ρ1, lt_min hδ0 hρ1, min_le_left _ _, min_le_right _ _⟩
  have hball : Metric.ball y ρ ⊆ effDom (conj g) :=
    (Metric.ball_subset_ball hρ0).trans hball0
  have hFy : conj g y = (((conj g y).toReal : ℝ) : EReal) :=
    h33_conj_coe g hbot hne y (hball (Metric.mem_ball_self hρ))
  obtain ⟨F, hF⟩ : ∃ F : ℝ, conj g y = (F : EReal) := ⟨_, hFy⟩
  have hcoer : ∀ s (c : ℝ), g s = c → ρ / 2 * ‖s‖ - (F + 1) ≤ c - inner ℝ y s := by
    intro s c hc
    by_cases hs : s = 0
    · subst hs
      have := h33_young_real g y 0 c F hc hF
      simp only [inner_zero_right, norm_zero, mul_zero, sub_zero, zero_sub] at this ⊢
      linarith
    · have hsn : 0 < ‖s‖ := norm_pos_iff.2 hs
      have htpos : 0 < ρ / 2 / ‖s‖ := by positivity
      have hnorm : ‖(ρ / 2 / ‖s‖) • s‖ = ρ / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]; field_simp
      have hmem : y + (ρ / 2 / ‖s‖) • s ∈ Metric.ball y ρ := by
        rw [Metric.mem_ball, dist_eq_norm]
        have : y + (ρ / 2 / ‖s‖) • s - y = (ρ / 2 / ‖s‖) • s := by abel
        rw [this, hnorm]; linarith
      have e := hρ1' (lt_of_lt_of_le (Metric.mem_ball.1 hmem) hρ1'')
      rw [Real.dist_eq, abs_lt] at e
      have hc'' := h33_conj_coe g hbot hne _ (hball hmem)
      have := h33_young_real g _ s c _ hc hc''
      rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at this
      have e3 : ρ / 2 / ‖s‖ * ‖s‖ ^ 2 = ρ / 2 * ‖s‖ := by field_simp
      have hFeq : (conj g y).toReal = F := by rw [hF]; rfl
      rw [hFeq] at e
      nlinarith [e.1, e.2]
  obtain ⟨s0, hs0⟩ := hne
  lift g s0 to ℝ using ⟨hs0, hbot s0⟩ with c0 hc0
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = c0 - inner ℝ y s0 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = max ‖s0‖ (2 * (M + (F + 1)) / ρ) + 1 := ⟨_, rfl⟩
  have hR1 : ‖s0‖ ≤ R := by rw [hR]; linarith [le_max_left ‖s0‖ (2 * (M + (F + 1)) / ρ)]
  have hR2 : 2 * (M + (F + 1)) / ρ < R := by
    rw [hR]; linarith [le_max_right ‖s0‖ (2 * (M + (F + 1)) / ρ)]
  let φ : EuclideanSpace ℝ (Fin n) → EReal := fun s => g s + ((-(inner ℝ y s) : ℝ) : EReal)
  have hφ : LowerSemicontinuous φ := by
    refine LowerSemicontinuous.add' hg.2.2.1 (Continuous.lowerSemicontinuous ?_)
      (fun s => EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _)))
    exact continuous_coe_real_ereal.comp (continuous_const.inner continuous_id).neg
  have hφc : ∀ s (c : ℝ), g s = c → φ s = ((c - inner ℝ y s : ℝ) : EReal) := by
    intro s c hc
    show g s + ((-(inner ℝ y s) : ℝ) : EReal) = _
    rw [hc, ← EReal.coe_add]; congr 1
  have hφt : ∀ s, g s = ⊤ → φ s = ⊤ := by
    intro s hs
    show g s + ((-(inner ℝ y s) : ℝ) : EReal) = _
    rw [hs]; exact EReal.top_add_coe _
  have hK : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R).Nonempty :=
    ⟨s0, by rw [mem_closedBall_zero_iff]; exact hR1⟩
  obtain ⟨sstar, hsK, hmin⟩ := (hφ.lowerSemicontinuousOn (Metric.closedBall 0 R)).exists_isMinOn
    hK (isCompact_closedBall _ _)
  have hφ0 : φ s0 = (M : EReal) := by rw [hφc s0 c0 hc0.symm, hM]
  have hle0 : φ sstar ≤ (M : EReal) := by
    rw [← hφ0]
    exact hmin (by rw [mem_closedBall_zero_iff]; exact hR1)
  have hglob : ∀ s, φ sstar ≤ φ s := by
    intro s
    by_cases hsK : s ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R
    · exact hmin hsK
    · rw [mem_closedBall_zero_iff, not_le] at hsK
      rcases eq_or_ne (g s) ⊤ with hs | hs
      · rw [hφt s hs]; exact le_top
      lift g s to ℝ using ⟨hs, hbot s⟩ with c hc
      rw [hφc s c hc.symm]
      refine hle0.trans ?_
      rw [EReal.coe_le_coe_iff]
      have h1 := hcoer s c hc.symm
      have h2 : 2 * (M + (F + 1)) / ρ * ρ = 2 * (M + (F + 1)) := by field_simp
      have h3 : 2 * (M + (F + 1)) < R * ρ := by
        have := mul_lt_mul_of_pos_right hR2 hρ
        linarith
      nlinarith
  have hne2 : g sstar ≠ ⊤ := by
    intro h
    have := hφt sstar h
    rw [this] at hle0
    exact absurd hle0 (by simp)
  lift g sstar to ℝ using ⟨hne2, hbot sstar⟩ with cs hcs
  refine ⟨sstar, h33_subgrad_of_min g hbot y sstar cs hcs.symm ?_⟩
  intro s c' hs
  have := hglob s
  rw [hφc sstar cs hcs.symm, hφc s c' hs, EReal.coe_le_coe_iff] at this
  exact this

end Ex

section Main
variable {n : ℕ}

lemma h33_conj_of_subgrad (θ : EuclideanSpace ℝ (Fin n) → EReal)
    (hθ : ∀ x, θ x ≠ ⊥) (x y : EuclideanSpace ℝ (Fin n)) (a : ℝ) (hax : θ x = (a : EReal))
    (hy : y ∈ subdiff θ x) :
    conj θ y = ((inner ℝ y x - a : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro s
    have h1 := hy.2 s
    rw [hax] at h1
    cases hs : θ s with
    | bot => exact absurd hs (hθ s)
    | top => simp
    | coe c =>
      rw [hs] at h1
      have h2 : a + inner ℝ y (s - x) ≤ c := by exact_mod_cast h1
      rw [inner_sub_right] at h2
      rw [← EReal.coe_sub]
      exact_mod_cast (by linarith)
  · refine le_trans ?_ (le_iSup _ x)
    rw [hax]
    exact le_rfl

lemma h33_dcSub_coe (f k : EuclideanSpace ℝ (Fin n) → EReal) (x : EuclideanSpace ℝ (Fin n))
    (a b : ℝ) (ha : f x = a) (hb : k x = b) : dcSub f k x = ((a - b : ℝ) : EReal) := by
  unfold dcSub
  rw [ha, hb]; simp [← EReal.coe_sub]

lemma h33_exists_nhds (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hgh : DCStanding g h) (ys : EuclideanSpace ℝ (Fin n)) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (h12a : ys ∈ interior (effDom (conj g)))
    (h12b : subdiff (conj g) ys ⊆ U) :
    ∃ V ∈ 𝓝 ys, V ⊆ interior (effDom (conj g)) ∧
      ∀ y ∈ V, subdiff (conj g) y ⊆ U ∩ effDom g := by
  obtain ⟨V0, hV0, hV0'⟩ := h33_usc g hgh.g_mem ys U hU h12a h12b
  refine ⟨V0 ∩ interior (effDom (conj g)), Filter.inter_mem hV0 (isOpen_interior.mem_nhds h12a),
    Set.inter_subset_right, fun y hy x hx => ?_⟩
  refine ⟨hV0' y hy.1 hx, ?_⟩
  obtain ⟨c, A, hc, -, -⟩ := h33_mem_dom g hgh.g_mem y x hx
  show g x ≠ ⊤
  rw [hc]; exact EReal.coe_ne_top _

lemma h33_cor_core (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hgh : DCStanding g h) (xs ys : EuclideanSpace ℝ (Fin n)) (hfin : xs ∈ effDom g)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hxU : xs ∈ U)
    (hmin : ∀ x ∈ U, x ∈ effDom g → dcSub g h xs ≤ dcSub g h x)
    (hy : ys ∈ subdiff h xs)
    (h12a : ys ∈ interior (effDom (conj g)))
    (h12b : subdiff (conj g) ys ⊆ U) :
    IsDCLocalMin (conj h) (conj g) ys := by
  have hgm := hgh.g_mem
  have hhm := hgh.h_mem
  have hgbot := hgm.1
  have hgne := hgm.2.1
  have hhbot := hhm.1
  have hhne := hhm.2.1
  obtain ⟨V, hV, hVint, hVsub⟩ := h33_exists_nhds g h hgh ys U hU h12a h12b
  -- values at xs, ys
  have hgxs : g xs ≠ ⊤ := hfin
  have hhxs : h xs ≠ ⊤ := hgh.dom_g_sub hfin
  obtain ⟨a, ha⟩ : ∃ a : ℝ, g xs = (a : EReal) := ⟨_, (EReal.coe_toReal hgxs (hgbot xs)).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, h xs = (b : EReal) := ⟨_, (EReal.coe_toReal hhxs (hhbot xs)).symm⟩
  have hchys := h33_conj_of_subgrad h hhbot xs ys b hb hy
  have hgys : conj g ys ≠ ⊤ := interior_subset h12a
  obtain ⟨A, hA⟩ : ∃ A : ℝ, conj g ys = (A : EReal) :=
    ⟨_, h33_conj_coe g hgbot hgne ys hgys⟩
  have hyoung : inner ℝ ys xs - a ≤ A := h33_young_real g ys xs a A ha hA
  have hvalD : dcSub (conj h) (conj g) ys = (((inner ℝ ys xs - b) - A : ℝ) : EReal) :=
    h33_dcSub_coe _ _ ys _ _ hchys hA
  have hvalP : dcSub g h xs = ((a - b : ℝ) : EReal) := h33_dcSub_coe g h xs a b ha hb
  refine ⟨by rw [hvalD]; exact EReal.coe_ne_top _, by rw [hvalD]; exact EReal.coe_ne_bot _,
    V, hV, fun z hz => ?_⟩
  rw [hvalD]
  rcases eq_or_ne (conj h z) ⊤ with hzt | hzt
  · have : dcSub (conj h) (conj g) z = ⊤ := by unfold dcSub; simp [hzt]
    rw [this]; exact le_top
  have hzint : z ∈ interior (effDom (conj g)) := hVint hz
  obtain ⟨x, hx⟩ := h33_exists_subgrad g hgm z hzint
  obtain ⟨hxU, hxdom⟩ := hVsub z hz hx
  obtain ⟨c, B, hc, hB, hBeq⟩ := h33_mem_dom g hgm z x hx
  have hhx : h x ≠ ⊤ := hgh.dom_g_sub hxdom
  obtain ⟨d, hd⟩ : ∃ d : ℝ, h x = (d : EReal) := ⟨_, (EReal.coe_toReal hhx (hhbot x)).symm⟩
  obtain ⟨H, hH⟩ : ∃ H : ℝ, conj h z = (H : EReal) :=
    ⟨_, (EReal.coe_toReal hzt (h33_conj_ne_bot h hhbot hhne z)).symm⟩
  have hyoungH : inner ℝ z x - d ≤ H := h33_young_real h z x d H hd hH
  have hvalz : dcSub (conj h) (conj g) z = ((H - B : ℝ) : EReal) := h33_dcSub_coe _ _ z _ _ hH hB
  have hvalx : dcSub g h x = ((c - d : ℝ) : EReal) := h33_dcSub_coe g h x c d hc hd
  have hm := hmin x hxU hxdom
  rw [hvalP, hvalx, EReal.coe_le_coe_iff] at hm
  rw [hvalz, EReal.coe_le_coe_iff]
  linarith

end Main

end TaoAnDCA.LocalOpt

open TaoAnDCA.LocalOpt


theorem solution {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hgh : TaoAnDCA.GlobalOpt.DCStanding g h) (ys : EuclideanSpace ℝ (Fin n)) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (h12a : ys ∈ interior (TaoAnDCA.GlobalOpt.effDom (CondatPD.FinDim.conj g)))
    (h12b : TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj g) ys ⊆ U) :
    ∃ V ∈ 𝓝 ys, V ⊆ interior (TaoAnDCA.GlobalOpt.effDom (CondatPD.FinDim.conj g)) ∧
      ∀ y ∈ V, TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj g) y ⊆ U ∩ TaoAnDCA.GlobalOpt.effDom g := by
  exact h33_exists_nhds g h hgh ys U hU h12a h12b
