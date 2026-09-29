-- Prove2me | solution 1 for RelaxationMethod.ConvexDomain.theorem3_case1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:00:01.515758+00:00
-- url     : https://prove2.me/submissions/027787fa-d4b7-4b50-85b0-3e80a5bde61f

import Mathlib
import Definitions.Def_RelaxationMethod_ConvexDomain_ImageProcess
import Definitions.Def_RelaxationMethod_Shared_FejerMonotone

open Filter Topology

namespace RelaxationMethod.ConvexDomain

theorem l1_eq_of_dist_eq {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hspan : affineSpan ℝ A = ⊤) (l l' : EuclideanSpace ℝ (Fin n))
    (h : ∀ a ∈ A, dist l a = dist l' a) : l = l' := by
  obtain ⟨a₀, ha₀⟩ : A.Nonempty := by
    rw [← affineSpan_nonempty (k := ℝ), hspan]; exact ⟨0, trivial⟩
  have key : ∀ a ∈ A, inner ℝ (l - l') (a - a₀) = 0 := by
    intro a ha
    have h1 := h a ha
    have h2 := h a₀ ha₀
    rw [dist_eq_norm, dist_eq_norm] at h1 h2
    have e1 : ‖(l - a₀) - (a - a₀)‖^2 = ‖(l' - a₀) - (a - a₀)‖^2 := by
      rw [sub_sub_sub_cancel_right, sub_sub_sub_cancel_right, h1]
    rw [norm_sub_sq_real (l - a₀) (a - a₀), norm_sub_sq_real (l' - a₀) (a - a₀), h2] at e1
    rw [inner_sub_left]
    have : inner ℝ (l - a₀) (a - a₀) - inner ℝ (l' - a₀) (a - a₀) = inner ℝ (l - l') (a - a₀) := by
      rw [← inner_sub_left]; congr 1; abel
    rw [inner_sub_left, inner_sub_left, inner_sub_left] at this
    simp only [inner_sub_left] at e1 ⊢
    linarith
  have hv : vectorSpan ℝ A = ⊤ := by
    rw [← direction_affineSpan, hspan, AffineSubspace.direction_top]
  rw [vectorSpan_eq_span_vsub_set_right ℝ ha₀] at hv
  have hle : Submodule.span ℝ ((· -ᵥ a₀) '' A) ≤ LinearMap.ker (innerₛₗ ℝ (l - l')) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub]
    exact key a ha
  rw [hv] at hle
  have hmem : l - l' ∈ LinearMap.ker (innerₛₗ ℝ (l - l')) := hle Submodule.mem_top
  simp only [LinearMap.mem_ker] at hmem
  change inner ℝ (l - l') (l - l') = 0 at hmem
  rw [inner_self_eq_zero, sub_eq_zero] at hmem
  exact hmem

theorem lemma1_case1_core {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hspan : affineSpan ℝ A = ⊤) (q : ℕ → EuclideanSpace ℝ (Fin n))
    (hq : RelaxationMethod.Shared.IsFejerMonotone A q) :
    ∃ l : EuclideanSpace ℝ (Fin n), Tendsto q atTop (𝓝 l) := by
  obtain ⟨a₀, ha₀⟩ : A.Nonempty := by
    rw [← affineSpan_nonempty (k := ℝ), hspan]; exact ⟨0, trivial⟩
  obtain ⟨-, -, hmono⟩ := hq
  have hanti : ∀ a ∈ A, Antitone (fun ν => dist (q ν) a) :=
    fun a ha => antitone_nat_of_succ_le (hmono a ha)
  have hconv : ∀ a ∈ A, Tendsto (fun ν => dist (q ν) a) atTop (𝓝 (⨅ ν, dist (q ν) a)) :=
    fun a ha => tendsto_atTop_ciInf (hanti a ha) ⟨0, by rintro _ ⟨ν, rfl⟩; exact dist_nonneg⟩
  have hbd : ∀ ν, q ν ∈ Metric.closedBall a₀ (dist (q 0) a₀) :=
    fun ν => hanti a₀ ha₀ (Nat.zero_le ν)
  have hlim : ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop → ∀ l', Tendsto (q ∘ φ) atTop (𝓝 l') →
      ∀ a ∈ A, dist l' a = ⨅ ν, dist (q ν) a := by
    intro φ hφ l' hl a ha
    exact tendsto_nhds_unique (hl.dist tendsto_const_nhds) ((hconv a ha).comp hφ)
  obtain ⟨l, -, ψ, hψ, hl⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hbd
  refine ⟨l, ?_⟩
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨l', -, φ, hφ, hl'⟩ :=
    tendsto_subseq_of_bounded Metric.isBounded_closedBall (fun k => hbd (ns k))
  have : l' = l := l1_eq_of_dist_eq A hspan l' l (fun a ha => by
    rw [hlim (ns ∘ φ) (hns.comp hφ.tendsto_atTop) l' hl' a ha,
      hlim ψ hψ.tendsto_atTop l hl a ha])
  exact ⟨φ, this ▸ hl'⟩

theorem rm_vi {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin n))} (hconv : Convex ℝ A)
    {p q : EuclideanSpace ℝ (Fin n)} (hq : IsNearestPoint A p q) :
    ∀ a ∈ A, inner ℝ (p - q) (a - q) ≤ 0 := by
  have : Nonempty A := ⟨⟨q, hq.1⟩⟩
  refine (norm_eq_iInf_iff_real_inner_le_zero (F := EuclideanSpace ℝ (Fin n)) hconv hq.1).mp ?_
  apply le_antisymm
  · apply le_ciInf
    intro w
    have := hq.2 w w.2
    rwa [dist_eq_norm, dist_eq_norm] at this
  · have hb : BddBelow (Set.range (fun w : A => ‖p - (w : EuclideanSpace ℝ (Fin n))‖)) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨w, rfl⟩
      exact norm_nonneg _
    exact ciInf_le hb (⟨q, hq.1⟩ : A)

theorem t3_step_id {n : ℕ} (p q p₁ y : EuclideanSpace ℝ (Fin n))
    (h : p₁ = p + (2 : ℝ) • (q - p)) :
    ‖p - y‖ ^ 2 - ‖p₁ - y‖ ^ 2 = 4 * inner ℝ (p - q) (q - y) := by
  have e1 : p - y = (p - q) + (q - y) := by abel
  have e2 : p₁ - y = (q - y) - (p - q) := by rw [h]; module
  rw [e1, e2, norm_add_sq_real (p - q) (q - y), norm_sub_sq_real (q - y) (p - q),
    real_inner_comm (q - y) (p - q)]
  ring

theorem t3c1_core {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hclosed : IsClosed A) (hconv : Convex ℝ A) (hspan : affineSpan ℝ A = ⊤)
    (p : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsImageRun A p) :
    ∃ N : ℕ, p N ∈ A := by
  by_contra hcon
  push Not at hcon
  have hinf : ∀ ν, p ν ∉ A := hcon
  choose q hq hstep using fun ν => hrun ν (hinf ν)
  have hvi : ∀ ν, ∀ a ∈ A, inner ℝ (p ν - q ν) (a - q ν) ≤ 0 := fun ν => rm_vi hconv (hq ν)
  have hid : ∀ ν y, ‖p ν - y‖ ^ 2 - ‖p (ν + 1) - y‖ ^ 2 = 4 * inner ℝ (p ν - q ν) (q ν - y) :=
    fun ν y => t3_step_id _ _ _ y (hstep ν)
  have hne : ∀ ν, p ν ≠ q ν := fun ν h => hinf ν (h ▸ (hq ν).1)
  have hdec : ∀ ν, ∀ a ∈ A, dist (p (ν + 1)) a ≤ dist (p ν) a := by
    intro ν a ha
    have h1 := hid ν a
    have h2 := hvi ν a ha
    have e : inner ℝ (p ν - q ν) (q ν - a) = - inner ℝ (p ν - q ν) (a - q ν) := by
      rw [← inner_neg_right, neg_sub]
    rw [dist_eq_norm, dist_eq_norm]
    have : ‖p (ν + 1) - a‖ ^ 2 ≤ ‖p ν - a‖ ^ 2 := by linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  have hF : RelaxationMethod.Shared.IsFejerMonotone A p := by
    refine ⟨hinf, fun ν h => ?_, fun a ha ν => hdec ν a ha⟩
    apply hne ν
    have := hstep ν
    rw [← h] at this
    have h2 : (2 : ℝ) • (q ν - p ν) = 0 := by
      have := congrArg (fun x => x - p ν) this; simpa using this.symm
    rw [smul_eq_zero] at h2
    rcases h2 with h2 | h2
    · norm_num at h2
    · exact (sub_eq_zero.mp h2).symm
  obtain ⟨l, hl⟩ := lemma1_case1_core A hspan p hF
  have hqeq : ∀ ν, q ν = (1 / 2 : ℝ) • (p ν + p (ν + 1)) := by
    intro ν; rw [hstep ν]; module
  have hql : Tendsto q atTop (𝓝 l) := by
    have := (hl.add (hl.comp (tendsto_add_atTop_nat 1))).const_smul (1 / 2 : ℝ)
    have e : (1 / 2 : ℝ) • (l + l) = l := by module
    rw [e] at this
    refine this.congr (fun ν => ?_)
    rw [hqeq ν]; rfl
  have hlA : l ∈ A := hclosed.mem_of_tendsto hql (Eventually.of_forall fun ν => (hq ν).1)
  -- h ≥ 0 and |q - l| ≤ |p - l|
  have hh0 : ∀ ν, 0 ≤ inner ℝ (p ν - q ν) (q ν - l) := by
    intro ν
    have := hvi ν l hlA
    have e : inner ℝ (p ν - q ν) (q ν - l) = - inner ℝ (p ν - q ν) (l - q ν) := by
      rw [← inner_neg_right, neg_sub]
    linarith
  have hql_le : ∀ ν, ‖q ν - l‖ ≤ ‖p ν - l‖ := by
    intro ν
    have e : p ν - l = (p ν - q ν) + (q ν - l) := by abel
    have h2 : ‖q ν - l‖ ^ 2 ≤ ‖p ν - l‖ ^ 2 := by
      rw [e, norm_add_sq_real]; nlinarith [hh0 ν, norm_nonneg (p ν - q ν)]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  have hsanti : Antitone (fun ν => ‖p ν - l‖) := by
    apply antitone_nat_of_succ_le
    intro ν
    have := hdec ν l hlA
    rwa [dist_eq_norm, dist_eq_norm] at this
  have hspos : ∀ ν, 0 < ‖p ν - l‖ := by
    intro ν
    rw [norm_pos_iff, sub_ne_zero]
    intro h; exact hinf ν (h ▸ hlA)
  -- interior ball
  obtain ⟨c, hc⟩ : (interior A).Nonempty := hconv.interior_nonempty_iff_affineSpan_eq_top.mpr hspan
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior c hc
  set r' : ℝ := r / 2 with hr'
  have hr'pos : 0 < r' := by positivity
  have hcb : Metric.closedBall c r' ⊆ A :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans (hball.trans interior_subset)
  have hcdec : ∀ ν, r' * ‖p ν - q ν‖ ≤ inner ℝ (p ν - q ν) (q ν - c) := by
    intro ν
    have hd : 0 < ‖p ν - q ν‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hne ν))
    have ha : c + (r' / ‖p ν - q ν‖) • (p ν - q ν) ∈ A := by
      apply hcb
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity), div_mul_cancel₀ _ hd.ne']
    have := hvi ν _ ha
    have e : c + (r' / ‖p ν - q ν‖) • (p ν - q ν) - q ν
        = (r' / ‖p ν - q ν‖) • (p ν - q ν) - (q ν - c) := by abel
    rw [e, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq] at this
    have e2 : r' / ‖p ν - q ν‖ * ‖p ν - q ν‖ ^ 2 = r' * ‖p ν - q ν‖ := by
      field_simp
    linarith
  -- smallness of h
  have hsmall : ∀ ε > 0, ∀ᶠ ν in atTop,
      inner ℝ (p ν - q ν) (q ν - l) ≤ ε * ‖p ν - q ν‖ * ‖q ν - l‖ := by
    intro ε hε
    by_contra hcon2
    rw [not_eventually] at hcon2
    obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop hcon2
    simp only [not_le] at hP
    have htpos : ∀ k, 0 < ‖q (φ k) - l‖ := by
      intro k
      rcases (norm_nonneg (q (φ k) - l)).lt_or_eq with h | h
      · exact h
      · exfalso
        have h0 : q (φ k) - l = 0 := norm_eq_zero.mp h.symm
        have := hP k
        rw [h0, inner_zero_right] at this; simp at this
    have hdpos : ∀ k, 0 < ‖p (φ k) - q (φ k)‖ :=
      fun k => norm_pos_iff.mpr (sub_ne_zero.mpr (hne (φ k)))
    set e : ℕ → EuclideanSpace ℝ (Fin n) :=
      fun k => ‖p (φ k) - q (φ k)‖⁻¹ • (p (φ k) - q (φ k)) with he
    set w : ℕ → EuclideanSpace ℝ (Fin n) :=
      fun k => ‖q (φ k) - l‖⁻¹ • (q (φ k) - l) with hw
    have heb : ∀ k, e k ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      intro k
      rw [Metric.mem_closedBall, dist_zero_right, he]
      simp only
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hdpos k).ne']
    have hwb : ∀ k, w k ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      intro k
      rw [Metric.mem_closedBall, dist_zero_right, hw]
      simp only
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (htpos k).ne']
    have hew : ∀ k, ε < inner ℝ (e k) (w k) := by
      intro k
      rw [he, hw]
      simp only
      rw [inner_smul_left, inner_smul_right]
      simp only [conj_trivial]
      have := hP k
      have hd := hdpos k
      have ht := htpos k
      have e1 : ‖p (φ k) - q (φ k)‖⁻¹ * (‖q (φ k) - l‖⁻¹ * inner ℝ (p (φ k) - q (φ k)) (q (φ k) - l))
          = inner ℝ (p (φ k) - q (φ k)) (q (φ k) - l) / (‖p (φ k) - q (φ k)‖ * ‖q (φ k) - l‖) := by
        field_simp
      rw [e1, lt_div_iff₀ (by positivity)]
      linarith
    obtain ⟨e', -, ψ1, hψ1, he1⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall heb
    obtain ⟨w', -, ψ2, hψ2, hw2⟩ :=
      tendsto_subseq_of_bounded Metric.isBounded_closedBall (fun k => hwb (ψ1 k))
    have he2 : Tendsto (fun k => e (ψ1 (ψ2 k))) atTop (𝓝 e') := he1.comp hψ2.tendsto_atTop
    have hw2' : Tendsto (fun k => w (ψ1 (ψ2 k))) atTop (𝓝 w') := hw2
    have hθ : Tendsto (fun k => φ (ψ1 (ψ2 k))) atTop atTop :=
      hφ.tendsto_atTop.comp (hψ1.tendsto_atTop.comp hψ2.tendsto_atTop)
    have hge : ε ≤ inner ℝ e' w' :=
      ge_of_tendsto (he2.inner hw2') (Eventually.of_forall fun k => (hew _).le)
    have hNc : ∀ y ∈ A, inner ℝ e' (y - l) ≤ 0 := by
      intro y hy
      have hT : Tendsto (fun k => inner ℝ (e (ψ1 (ψ2 k))) (y - q (φ (ψ1 (ψ2 k))))) atTop
          (𝓝 (inner ℝ e' (y - l))) :=
        he2.inner (tendsto_const_nhds.sub (hql.comp hθ))
      refine le_of_tendsto hT (Eventually.of_forall fun k => ?_)
      rw [he]
      simp only
      rw [inner_smul_left]
      simp only [conj_trivial]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hvi _ y hy)
    have hle : inner ℝ e' w' ≤ 0 := by
      refine le_of_tendsto (tendsto_const_nhds.inner hw2') (Eventually.of_forall fun k => ?_)
      rw [hw]
      simp only
      rw [inner_smul_right]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hNc _ (hq _).1)
    linarith
  -- final estimate
  set K : ℝ := ‖p 0 - l‖ + 2 * ‖l - c‖ + 1 with hK
  have hKpos : 0 < K := by positivity
  set ε : ℝ := r' / (2 * K) with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hsmall ε hεpos)
  set sN : ℝ := ‖p N - l‖ with hsN
  set X : ℝ := ε * sN / r' with hX
  have hXnn : 0 ≤ X := by have := hspos N; positivity
  have hind : ∀ M ≥ N, sN ^ 2 - ‖p M - l‖ ^ 2 ≤ X * (‖p N - c‖ ^ 2 - ‖p M - c‖ ^ 2) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => rw [hsN]; simp
    | succ M hMN ih =>
      have a1 := hid M l
      have a2 := hid M c
      have a3 := hN M hMN
      have a4 := hcdec M
      have a5 := hql_le M
      have a6 : ‖p M - l‖ ≤ sN := hsanti hMN
      have hd := norm_nonneg (p M - q M)
      have k1 : inner ℝ (p M - q M) (q M - l) ≤ ε * ‖p M - q M‖ * sN :=
        a3.trans (mul_le_mul_of_nonneg_left (a5.trans a6) (by positivity))
      have k2 : ε * ‖p M - q M‖ * sN ≤ X * inner ℝ (p M - q M) (q M - c) := by
        have : X * (r' * ‖p M - q M‖) = ε * ‖p M - q M‖ * sN := by
          rw [hX]; field_simp
        rw [← this]
        exact mul_le_mul_of_nonneg_left a4 hXnn
      have a2' : X * (‖p M - c‖ ^ 2 - ‖p (M + 1) - c‖ ^ 2)
          = X * (4 * inner ℝ (p M - q M) (q M - c)) := by rw [a2]
      nlinarith
  have hT1 : Tendsto (fun M => sN ^ 2 - ‖p M - l‖ ^ 2 - X * (‖p N - c‖ ^ 2 - ‖p M - c‖ ^ 2))
      atTop (𝓝 (sN ^ 2 - 0 ^ 2 - X * (‖p N - c‖ ^ 2 - ‖l - c‖ ^ 2))) := by
    have h1 : Tendsto (fun M => ‖p M - l‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hl
    have h2 : Tendsto (fun M => ‖p M - c‖) atTop (𝓝 ‖l - c‖) := (hl.sub_const c).norm
    exact (tendsto_const_nhds.sub (h1.pow 2)).sub
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub (h2.pow 2)))
  have hlim : sN ^ 2 - 0 ^ 2 - X * (‖p N - c‖ ^ 2 - ‖l - c‖ ^ 2) ≤ 0 :=
    le_of_tendsto hT1 (eventually_atTop.mpr ⟨N, fun M hM => by linarith [hind M hM]⟩)
  have hY : ‖p N - c‖ ^ 2 - ‖l - c‖ ^ 2 ≤ sN * K := by
    have e : p N - c = (p N - l) + (l - c) := by abel
    rw [e, norm_add_sq_real]
    have := real_inner_le_norm (p N - l) (l - c)
    have h0 : sN ≤ ‖p 0 - l‖ := hsanti (Nat.zero_le N)
    have hs := hspos N
    rw [← hsN] at this ⊢
    nlinarith [norm_nonneg (l - c)]
  have hXK : X * (sN * K) = sN ^ 2 / 2 := by
    rw [hX, hε]; field_simp
  have hs := hspos N
  rw [← hsN] at hs
  have : X * (‖p N - c‖ ^ 2 - ‖l - c‖ ^ 2) ≤ X * (sN * K) := mul_le_mul_of_nonneg_left hY hXnn
  nlinarith

end RelaxationMethod.ConvexDomain

open RelaxationMethod.ConvexDomain
open Filter Topology

theorem solution {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hbdd : Bornology.IsBounded A) (hspan : affineSpan ℝ A = ⊤)
    (p : ℕ → EuclideanSpace ℝ (Fin n)) (h0 : p 0 ∉ A) (hrun : IsImageRun A p) :
    ∃ N : ℕ, p N ∈ A := by
  exact t3c1_core A hclosed hconv hspan p hrun
