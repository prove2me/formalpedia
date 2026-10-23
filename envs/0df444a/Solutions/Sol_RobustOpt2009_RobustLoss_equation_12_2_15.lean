-- Prove2me | solution 1 for RobustOpt2009.RobustLoss.equation_12_2_15
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:05:00.460991+00:00
-- url     : https://prove2.me/submissions/48d1ea92-7a3a-43d4-8266-81558f7f6ad1

import Mathlib
import Definitions.Def_fenchelConjugate

open scoped RealInnerProductSpace
open ConvexOptimization

namespace X5RL

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

/-- Subgradient of a finite convex function on `ℝ^m`. -/
theorem exists_subgrad (L : E → ℝ) (hconv : ConvexOn ℝ Set.univ L) (x0 : E) :
    ∃ v : E, ∀ y : E, L x0 + ⟪v, y - x0⟫ ≤ L y := by
  have hcont : Continuous L := by
    have := hconv.continuousOn isOpen_univ
    exact continuousOn_univ.mp this
  set s : Set (E × ℝ) := {p | L p.1 < p.2} with hs
  have hopen : IsOpen s := isOpen_lt (hcont.comp continuous_fst) continuous_snd
  have hcvx : Convex ℝ s := by
    intro p hp q hq a b ha hb hab
    simp only [hs, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hp hq ⊢
    have h1 := hconv.2 (Set.mem_univ p.1) (Set.mem_univ q.1) ha hb hab
    simp only [smul_eq_mul] at h1
    rcases eq_or_lt_of_le ha with h | h
    · subst h
      have : b = 1 := by linarith
      subst this
      nlinarith
    · nlinarith [mul_lt_mul_of_pos_left hp h, mul_le_mul_of_nonneg_left hq.le hb]
  have hx : (x0, L x0) ∉ s := by simp [hs]
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hcvx hopen hx
  set g : E →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ E ℝ)
  set c : ℝ := f (0, 1)
  have hdec : ∀ y : E, ∀ t : ℝ, f (y, t) = g y + t * c := by
    intro y t
    have : (y, t) = (y, (0:ℝ)) + t • ((0 : E), (1:ℝ)) := by ext <;> simp
    rw [this, map_add, map_smul]
    simp [g, c]
  have hc : c < 0 := by
    have := hf (x0, L x0 + 1) (by simp [hs])
    rw [hdec, hdec] at this
    linarith
  have key : ∀ y : E, g y + L y * c ≤ g x0 + L x0 * c := by
    intro y
    by_contra h
    push Not at h
    set gap := g y + L y * c - (g x0 + L x0 * c)
    have hgap : 0 < gap := by simp only [gap]; linarith
    set ε := gap / (-c) / 2
    have hε : 0 < ε := div_pos (div_pos hgap (neg_pos.mpr hc)) two_pos
    have hc0 : c ≠ 0 := hc.ne
    have hεc : ε * c = -(gap / 2) := by
      simp only [ε]; field_simp
    have := hf (y, L y + ε) (by simp [hs, hε])
    rw [hdec, hdec] at this
    nlinarith
  refine ⟨(InnerProductSpace.toDual ℝ E).symm ((-c)⁻¹ • g), fun y => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, map_sub]
  have := key y
  have hc' : 0 < -c := by linarith
  have hc0 : c ≠ 0 := hc.ne
  rw [← sub_nonneg]
  have : L y - (L x0 + ((-c)⁻¹ * g y - (-c)⁻¹ * g x0)) = (-c)⁻¹ * ((g x0 + L x0 * c) - (g y + L y * c)) := by
    field_simp; ring
  rw [this]
  exact mul_nonneg (inv_nonneg.mpr hc'.le) (by linarith)

/-- Hahn–Banach for a sublinear `ψ`. -/
theorem exists_norming (ψ : E → ℝ) (hψ0 : ∀ v, 0 ≤ ψ v)
    (hψh : ∀ (t : ℝ) v, ψ (t • v) = |t| * ψ v)
    (hψa : ∀ v w, ψ (v + w) ≤ ψ v + ψ w) (v : E) :
    ∃ ξ : E, (∀ w, ⟪ξ, w⟫ ≤ ψ w) ∧ ⟪ξ, v⟫ = ψ v := by
  by_cases hv : v = 0
  · subst hv
    refine ⟨0, fun w => by simpa using hψ0 w, ?_⟩
    have := hψh 0 0
    simp at this
    simp [this]
  have H : ∀ c : ℝ, c • v = 0 → (RingHom.id ℝ) c • ψ v = 0 := by
    intro c hc
    rcases smul_eq_zero.mp hc with h | h
    · simp [h]
    · exact absurd h hv
  set f := LinearPMap.mkSpanSingleton' (σ := RingHom.id ℝ) v (ψ v) H
  have hf : ∀ x : f.domain, f x ≤ ψ x := by
    rintro ⟨x, hx⟩
    have hx' := hx
    change x ∈ Submodule.span ℝ {v} at hx'
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx'
    rw [LinearPMap.mkSpanSingleton'_apply]
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [hψh]
    exact mul_le_mul_of_nonneg_right (le_abs_self a) (hψ0 v)
  obtain ⟨g, hgf, hgle⟩ := exists_extension_of_le_sublinear f ψ
    (fun c hc x => by rw [hψh, abs_of_pos hc]) hψa hf
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap g), ?_, ?_⟩
  · intro w
    rw [InnerProductSpace.toDual_symm_apply]
    exact hgle w
  · rw [InnerProductSpace.toDual_symm_apply]
    have hmem : (1:ℝ) • v ∈ f.domain := by
      rw [one_smul]; exact Submodule.mem_span_singleton_self v
    have := hgf ⟨(1:ℝ) • v, hmem⟩
    rw [LinearPMap.mkSpanSingleton'_apply] at this
    simpa using this

/-- `ψ` is dominated by a multiple of the Euclidean norm. -/
theorem psi_le (ψ : E → ℝ) (hψ0 : ∀ v, 0 ≤ ψ v) (hψz : ψ 0 = 0)
    (hψh : ∀ (t : ℝ) v, ψ (t • v) = |t| * ψ v)
    (hψa : ∀ v w, ψ (v + w) ≤ ψ v + ψ w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ψ v ≤ C * ‖v‖ := by
  set b := EuclideanSpace.basisFun (Fin m) ℝ
  refine ⟨∑ i, ψ (b i), Finset.sum_nonneg (fun i _ => hψ0 _), fun v => ?_⟩
  have hv : v = ∑ i, (b.repr v).ofLp i • b i := (b.sum_repr v).symm
  calc ψ v = ψ (∑ i, (b.repr v).ofLp i • b i) := by rw [← hv]
    _ ≤ ∑ i, ψ ((b.repr v).ofLp i • b i) :=
        Finset.le_sum_of_subadditive ψ hψz.le hψa _ _
    _ = ∑ i, |(b.repr v).ofLp i| * ψ (b i) := by simp_rw [hψh]
    _ ≤ ∑ i, ‖v‖ * ψ (b i) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right _ (hψ0 _)
        have := PiLp.norm_apply_le (b.repr v) i
        rw [Real.norm_eq_abs] at this
        simpa [b.repr.norm_map] using this
    _ = (∑ i, ψ (b i)) * ‖v‖ := by rw [Finset.sum_mul]; simp_rw [mul_comm]

/-- The dual ball is compact. -/
theorem dualBall_compact (ψ : E → ℝ) (C : ℝ) (hC : ∀ v, ψ v ≤ C * ‖v‖) :
    IsCompact {ξ : E | ∀ v : E, ⟪ξ, v⟫ ≤ ψ v} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have : {ξ : E | ∀ v : E, ⟪ξ, v⟫ ≤ ψ v} = ⋂ v : E, {ξ : E | ⟪ξ, v⟫ ≤ ψ v} := by
      ext; simp
    rw [this]
    exact isClosed_iInter fun v => isClosed_le (continuous_id.inner continuous_const)
      continuous_const
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨max C 0, fun ξ hξ => ?_⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    have h1 := hξ ξ
    rw [real_inner_self_eq_norm_sq] at h1
    have h2 := hC ξ
    by_cases h : ‖ξ‖ = 0
    · rw [h]; exact le_max_right _ _
    · have hpos : 0 < ‖ξ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
      have : ‖ξ‖ ≤ C := by nlinarith
      exact this.trans (le_max_left _ _)

end X5RL



namespace X5RL

theorem core {m : ℕ} {X : Type*} [TopologicalSpace X]
    (L : EuclideanSpace ℝ (Fin m) → ℝ) (hconv : ConvexOn ℝ Set.univ L)
    (D : Set X) (hDk : IsCompact D) (hDne : D.Nonempty)
    (x : X → EuclideanSpace ℝ (Fin m)) (hx : Continuous x)
    (c : EuclideanSpace ℝ (Fin m) → ℝ)
    (h1 : ∀ v, ∀ Δ ∈ D, ⟪x Δ, v⟫ ≤ c v) (h2 : ∀ v, ∃ Δ ∈ D, ⟪x Δ, v⟫ = c v) :
    ∃ M : ℝ, IsGreatest ((fun Δ => L (x Δ)) '' D) M ∧
      IsGreatest {w : EReal | ∃ Δ ∈ D, ∃ v : EuclideanSpace ℝ (Fin m),
        w = ((⟪x Δ, v⟫ : ℝ) : EReal) - fenchelConjugate L v} (M : EReal) ∧
      IsGreatest (Set.range (fun v => ((c v : ℝ) : EReal) - fenchelConjugate L v)) (M : EReal) := by
  have hcont : Continuous L := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  obtain ⟨Δs, hΔs, hmax⟩ := hDk.exists_isMaxOn hDne (f := fun Δ => L (x Δ))
    (hcont.comp hx).continuousOn
  set M := L (x Δs)
  have fy : ∀ Δ v, ((⟪x Δ, v⟫ : ℝ) : EReal) - fenchelConjugate L v ≤ (L (x Δ) : EReal) := by
    intro Δ v
    have h := le_iSup (fun y => ((⟪y, v⟫ - L y : ℝ) : EReal)) (x Δ)
    have h' := EReal.sub_le_sub (le_refl ((⟪x Δ, v⟫ : ℝ) : EReal)) h
    refine h'.trans (le_of_eq ?_)
    rw [← EReal.coe_sub]; congr 1; ring
  obtain ⟨v0, hv0⟩ := exists_subgrad L hconv (x Δs)
  have hconj : fenchelConjugate L v0 = ((⟪x Δs, v0⟫ - M : ℝ) : EReal) := by
    apply le_antisymm
    · apply iSup_le
      intro y
      rw [EReal.coe_le_coe_iff]
      have := hv0 y
      rw [inner_sub_right] at this
      rw [real_inner_comm v0 y, real_inner_comm v0 (x Δs)] at *
      linarith
    · exact le_iSup (fun y => ((⟪y, v0⟫ - L y : ℝ) : EReal)) (x Δs)
  have hat : ((⟪x Δs, v0⟫ : ℝ) : EReal) - fenchelConjugate L v0 = (M : EReal) := by
    rw [hconj, ← EReal.coe_sub]; congr 1; ring
  refine ⟨M, ⟨⟨Δs, hΔs, rfl⟩, ?_⟩, ⟨⟨Δs, hΔs, v0, hat.symm⟩, ?_⟩, ⟨⟨v0, ?_⟩, ?_⟩⟩
  · rintro _ ⟨Δ, hΔ, rfl⟩; exact hmax hΔ
  · rintro _ ⟨Δ, hΔ, v, rfl⟩
    exact (fy Δ v).trans (EReal.coe_le_coe_iff.mpr (hmax hΔ))
  · apply le_antisymm
    · obtain ⟨Δ, hΔ, he⟩ := h2 v0
      show ((c v0 : ℝ) : EReal) - _ ≤ _
      rw [← he]; exact (fy Δ v0).trans (EReal.coe_le_coe_iff.mpr (hmax hΔ))
    · show _ ≤ ((c v0 : ℝ) : EReal) - _
      rw [← hat]
      exact EReal.sub_le_sub (EReal.coe_le_coe_iff.mpr (h1 v0 Δs hΔs)) le_rfl
  · rintro _ ⟨v, rfl⟩
    obtain ⟨Δ, hΔ, he⟩ := h2 v
    simp only
    rw [← he]; exact (fy Δ v).trans (EReal.coe_le_coe_iff.mpr (hmax hΔ))

example {m : ℕ} (f : Fin m → ℝ) (v : EuclideanSpace ℝ (Fin m)) :
    ⟪(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin m)), v⟫ = ∑ i, f i * v i := by
  simp [PiLp.inner_apply, mul_comm]

end X5RL



namespace X5RL

theorem inner_toLp {m : ℕ} (f : Fin m → ℝ) (v : EuclideanSpace ℝ (Fin m)) :
    ⟪(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin m)), v⟫ = ∑ i, f i * v i := by
  simp [PiLp.inner_apply, mul_comm]

theorem inner_x {n l m : ℕ}
    (Zn : Matrix (Fin n) (Fin m) ℝ) (U : Matrix (Fin n) (Fin l) ℝ) (ρ : ℝ)
    (θ : EuclideanSpace ℝ (Fin n)) (Δ : Matrix (Fin l) (Fin m) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) :
    ⟪(WithLp.toLp 2 (fun i => ∑ a, (Zn a i + ρ * ∑ b, U a b * Δ b i) * θ a) :
        EuclideanSpace ℝ (Fin m)), v⟫ =
      ⟪(WithLp.toLp 2 (fun i => ∑ a, Zn a i * θ a) : EuclideanSpace ℝ (Fin m)), v⟫ +
        ρ * ∑ a, ∑ b, ∑ i, θ a * U a b * Δ b i * v i := by
  rw [inner_toLp, inner_toLp]
  simp only [Finset.sum_mul, Finset.mul_sum, add_mul, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro i _
  ring

theorem cont_x {n l m : ℕ}
    (Zn : Matrix (Fin n) (Fin m) ℝ) (U : Matrix (Fin n) (Fin l) ℝ) (ρ : ℝ)
    (θ : EuclideanSpace ℝ (Fin n)) :
    Continuous (fun Δ : Matrix (Fin l) (Fin m) ℝ =>
      (WithLp.toLp 2 (fun i => ∑ a, (Zn a i + ρ * ∑ b, U a b * Δ b i) * θ a) :
        EuclideanSpace ℝ (Fin m))) := by
  apply (PiLp.continuous_toLp 2 _).comp
  fun_prop

end X5RL

theorem solution
    {n l m : ℕ} (hn : 0 < n) (hl : 0 < l) (hm : 0 < m)
    (Zn : Matrix (Fin n) (Fin m) ℝ) (U : Matrix (Fin n) (Fin l) ℝ)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (D : Set (Matrix (Fin l) (Fin m) ℝ))
    (hDc : Convex ℝ D) (hDk : IsCompact D) (hD0 : 0 ∈ D)
    (L : EuclideanSpace ℝ (Fin m) → ℝ)
    (hconv : ConvexOn ℝ Set.univ L)
    (hL : ∃ π : EuclideanSpace ℝ (Fin m) → ℝ,
      ConvexOn ℝ {x | ∀ i, 0 ≤ x i} π ∧
      (∀ x y, (∀ i, 0 ≤ x i) → (∀ i, x i ≤ y i) → π x ≤ π y) ∧
      ((∀ r, L r = π (WithLp.toLp 2 (fun i => |r i|))) ∨
       (∀ r, L r = π (WithLp.toLp 2 (fun i => max (r i) 0)))))
    (φ : EuclideanSpace ℝ (Fin l) → ℝ)
    (hφ0 : ∀ u, 0 ≤ φ u) (hφc : ConvexOn ℝ Set.univ φ)
    (hφh : ∀ t : ℝ, 0 ≤ t → ∀ u, φ (t • u) = t * φ u)
    (ψ : EuclideanSpace ℝ (Fin m) → ℝ)
    (hψ0 : ∀ v, 0 ≤ ψ v) (hψz : ∀ v, ψ v = 0 ↔ v = 0)
    (hψh : ∀ (t : ℝ) v, ψ (t • v) = |t| * ψ v)
    (hψa : ∀ v w, ψ (v + w) ≤ ψ v + ψ w)
    (hA : ∀ (u : EuclideanSpace ℝ (Fin l)) (v : EuclideanSpace ℝ (Fin m)),
      IsGreatest ((fun Δ : Matrix (Fin l) (Fin m) ℝ =>
        ∑ a, ∑ i, u a * Δ a i * v i) '' D) (φ u * ψ v))
    (θ : EuclideanSpace ℝ (Fin n)) :
    ∃ M : ℝ,
      IsGreatest ((fun Δ : Matrix (Fin l) (Fin m) ℝ =>
        L (WithLp.toLp 2 (fun i => ∑ a, (Zn a i + ρ * ∑ b, U a b * Δ b i) * θ a))) '' D) M ∧
      IsGreatest (Set.range (fun v : EuclideanSpace ℝ (Fin m) =>
        (((⟪(WithLp.toLp 2 (fun i => ∑ a, Zn a i * θ a)), v⟫ : ℝ) + ρ * φ (WithLp.toLp 2 (fun b => ∑ a, U a b * θ a)) * ψ v : ℝ) : EReal) -
          fenchelConjugate L v)) (M : EReal) := by
  set u : EuclideanSpace ℝ (Fin l) := WithLp.toLp 2 (fun b => ∑ a, U a b * θ a) with hu
  have hrel : ∀ (Δ : Matrix (Fin l) (Fin m) ℝ) (v : EuclideanSpace ℝ (Fin m)),
      ∑ a, ∑ b, ∑ i, θ a * U a b * Δ b i * v i = ∑ b, ∑ i, u b * Δ b i * v i := by
    intro Δ v
    simp only [hu, PiLp.toLp_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro a _
    ring
  have H1 : ∀ v : EuclideanSpace ℝ (Fin m), ∀ Δ ∈ D,
      ⟪(WithLp.toLp 2 (fun i => ∑ a, (Zn a i + ρ * ∑ b, U a b * Δ b i) * θ a) :
        EuclideanSpace ℝ (Fin m)), v⟫ ≤
      (⟪(WithLp.toLp 2 (fun i => ∑ a, Zn a i * θ a) : EuclideanSpace ℝ (Fin m)), v⟫ : ℝ) +
      ρ * φ u * ψ v := by
    intro v Δ hΔ
    rw [X5RL.inner_x, hrel, mul_assoc]
    gcongr
    exact (hA u v).2 (Set.mem_image_of_mem _ hΔ)
  have H2 : ∀ v : EuclideanSpace ℝ (Fin m), ∃ Δ ∈ D,
      ⟪(WithLp.toLp 2 (fun i => ∑ a, (Zn a i + ρ * ∑ b, U a b * Δ b i) * θ a) :
        EuclideanSpace ℝ (Fin m)), v⟫ =
      (⟪(WithLp.toLp 2 (fun i => ∑ a, Zn a i * θ a) : EuclideanSpace ℝ (Fin m)), v⟫ : ℝ) +
      ρ * φ u * ψ v := by
    intro v
    obtain ⟨Δ, hΔ, he⟩ := (hA u v).1
    simp only at he
    exact ⟨Δ, hΔ, by rw [X5RL.inner_x, hrel, he, mul_assoc]⟩
  obtain ⟨M, h1, -, h3⟩ := X5RL.core L hconv D hDk ⟨0, hD0⟩ _ (X5RL.cont_x Zn U ρ θ) _ H1 H2
  exact ⟨M, h1, h3⟩
