-- Prove2me | solution 1 for TsengCGD.ErrorBound.theorem4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T02:45:32.228821+00:00
-- url     : https://prove2.me/submissions/69ed00e7-49ad-4544-9aef-e6749cf83640
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TsengCGD_Linear_Basic
import Definitions.Def_TsengCGD_ErrorBound_Conditions
import Theorems.Thm_TsengCGD_ErrorBound_lemma6
import Theorems.Thm_TsengCGD_ErrorBound_lemma7
open Filter Topology
open scoped RealInnerProductSpace

namespace TsengT4Aux

/-- Extreme value theorem on a closed set with a coercivity condition. -/
theorem exists_min_closed {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {S : Set E} (hS : IsClosed S) {φ : E → ℝ} (hφ : ContinuousOn φ S) {z0 : E} (hz0 : z0 ∈ S)
    (R : ℝ) (hR : ∀ z ∈ S, R < ‖z‖ → φ z0 ≤ φ z) : ∃ z ∈ S, ∀ w ∈ S, φ z ≤ φ w := by
  have hc : ∀ᶠ x in cocompact E ⊓ 𝓟 S, φ z0 ≤ φ x := by
    refine mem_inf_of_inter (isCompact_closedBall (0 : E) R).compl_mem_cocompact
      (mem_principal_self S) ?_
    rintro z ⟨hz1, hz2⟩
    apply hR z hz2
    simpa [Metric.mem_closedBall, dist_zero_right] using hz1
  obtain ⟨z, hz, hmin⟩ := hφ.exists_isMinOn' hS hz0 hc
  exact ⟨z, hz, fun w hw => hmin hw⟩

open Classical in
/-- The epigraph of `P` (as a subset of `Vec n × ℝ`) is closed. -/
theorem isClosed_epi {n : ℕ} {D : Set (TsengCGD.Global.Vec n)} {P : TsengCGD.Global.Vec n → ℝ}
    (h : LowerSemicontinuous (fun x => if x ∈ D then (P x : EReal) else ⊤)) :
    IsClosed {p : TsengCGD.Global.Vec n × ℝ | p.1 ∈ D ∧ P p.1 ≤ p.2} := by
  have hE := h.isClosed_epigraph
  have hc : Continuous (fun p : TsengCGD.Global.Vec n × ℝ => (p.1, ((p.2 : ℝ) : EReal))) :=
    continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
  convert hE.preimage hc using 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  by_cases hp : p.1 ∈ D
  · simp [hp]
  · simp [hp]

end TsengT4Aux

namespace TsengT4Aux
open TsengCGD.Global TsengCGD.ErrorBound

/-- A polyhedral `P` is Lipschitz continuous on `dom P`. -/
theorem polyhedral_lip {n : ℕ} {D : Set (Vec n)} {P : Vec n → ℝ} (h : IsPolyhedral D P) :
    ∃ K, PLipOn D P K := by
  obtain ⟨m, a, b, e, hiff⟩ := h
  -- every `b i ≤ 0` (if `D` is nonempty)
  have hb : ∀ y ∈ D, ∀ i, b i ≤ 0 := by
    intro y hy i
    by_contra hpos
    push Not at hpos
    have h1 := (hiff y (P y + (|e i - ⟪a i, y⟫ - b i * P y| + 1) / b i)).1
      ⟨hy, by have : 0 ≤ (|e i - ⟪a i, y⟫ - b i * P y| + 1) / b i := by positivity
              linarith⟩ i
    rw [mul_add, mul_div_cancel₀ _ hpos.ne'] at h1
    have := le_abs_self (e i - ⟪a i, y⟫ - b i * P y)
    linarith
  set K : ℝ := ∑ i, ‖a i‖ / |b i|
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => by positivity
  have one_side : ∀ y ∈ D, ∀ z ∈ D, P y ≤ P z + K * ‖y - z‖ := by
    intro y hy z hz
    refine ((hiff y _).2 ?_).2
    intro i
    have hyi := (hiff y (P y)).1 ⟨hy, le_rfl⟩ i
    have hzi := (hiff z (P z)).1 ⟨hz, le_rfl⟩ i
    have hbi := hb y hy i
    rcases hbi.lt_or_eq with hlt | heq
    · have hKI : ‖a i‖ / |b i| ≤ K :=
        Finset.single_le_sum (f := fun i => ‖a i‖ / |b i|) (fun j _ => by positivity)
          (Finset.mem_univ i)
      have habs : |b i| = - b i := abs_of_neg hlt
      have h1 : ‖a i‖ ≤ K * (- b i) := by
        rw [← habs]; rwa [div_le_iff₀ (abs_pos.2 hlt.ne)] at hKI
      have h2 : ⟪a i, y - z⟫ ≤ ‖a i‖ * ‖y - z‖ := real_inner_le_norm _ _
      have h3 : ⟪a i, y⟫ = ⟪a i, z⟫ + ⟪a i, y - z⟫ := by
        rw [inner_sub_right]; ring
      have h4 : ‖a i‖ * ‖y - z‖ ≤ K * (- b i) * ‖y - z‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      nlinarith
    · rw [heq] at hyi ⊢; simpa using hyi
  refine ⟨K, hK, fun y hy z hz => abs_le.2 ⟨?_, ?_⟩⟩
  · have := one_side z hz y hy
    rw [norm_sub_rev] at this
    linarith
  · linarith [one_side y hy z hz]

open Classical in
/-- Existence of an optimal solution of the subproblem (42). -/
theorem exists_epiSubSol {n : ℕ} {f : Vec n → ℝ} {D : Set (Vec n)} {P : Vec n → ℝ} {c : ℝ}
    (hs : Standing f D P c) {x : Vec n} (hx : x ∈ D) :
    ∃ d δ, IsEpiSubSol f D P c x (P x) d δ := by
  have hlsc := hs.properConvexLsc.2.2.2
  set S : Set (Vec n × ℝ) := {p | x + p.1 ∈ D ∧ P (x + p.1) ≤ P x + p.2} with hSdef
  have hS : IsClosed S := by
    have := (isClosed_epi hlsc).preimage
      ((continuous_const.add continuous_fst).prodMk (continuous_const.add continuous_snd) :
        Continuous (fun p : Vec n × ℝ => (x + p.1, P x + p.2)))
    exact this
  set g := gradient f x
  set φ : Vec n × ℝ → ℝ := fun p => epiObj f c x p.1 p.2 with hφ
  have hφc : Continuous φ := by
    show Continuous (fun p : Vec n × ℝ => epiObj f c x p.1 p.2)
    unfold epiObj
    fun_prop
  have h0 : ((0 : Vec n), (0 : ℝ)) ∈ S := by simp [hSdef, hx]
  set A := ‖g‖ + |c|
  obtain ⟨z, hzS, hz⟩ := exists_min_closed hS hφc.continuousOn h0 (4 * A + 1) (by
    intro p _ hp
    rw [Prod.norm_def] at hp
    have hA : 0 ≤ A := by positivity
    have e1 : -(‖g‖ * ‖p.1‖) ≤ ⟪g, p.1⟫ := by
      have := abs_real_inner_le_norm g p.1; have := neg_abs_le ⟪g, p.1⟫; linarith
    have e2 : -(|c| * |p.2|) ≤ c * p.2 := by
      have := abs_mul c p.2; have := neg_abs_le (c * p.2); nlinarith [abs_nonneg (c * p.2)]
    have hn1 := norm_nonneg p.1
    have hn2 := abs_nonneg p.2
    have hsq : p.2 ^ 2 = |p.2| ^ 2 := (sq_abs _).symm
    have hc' := abs_nonneg c
    have hg' := norm_nonneg g
    show epiObj f c x 0 0 ≤ epiObj f c x p.1 p.2
    simp only [epiObj, inner_zero_right, norm_zero]
    simp only [Real.norm_eq_abs] at hp
    rw [hsq]
    have k1 : ∀ s a : ℝ, 0 ≤ a → a ≤ A → 0 ≤ s → -(A ^ 2 / 2) ≤ s ^ 2 / 2 - a * s := by
      intro s a ha haA hs0; nlinarith [sq_nonneg (s - a)]
    have k2 : ∀ s a : ℝ, 0 ≤ a → a ≤ A → 4 * A + 1 < s → A ^ 2 ≤ s ^ 2 / 2 - a * s := by
      intro s a ha haA hs0; nlinarith
    have hgA : ‖g‖ ≤ A := by simp only [A]; linarith
    have hcA : |c| ≤ A := by simp only [A]; linarith
    have e1' : -(‖g‖ * ‖p.1‖) ≤ ⟪gradient f x, p.1⟫ := e1
    rcases lt_max_iff.1 hp with h | h
    · have := k2 _ _ hg' hgA h; have := k1 _ _ hc' hcA hn2
      nlinarith [sq_nonneg A]
    · have := k1 _ _ hg' hgA hn1; have := k2 _ _ hc' hcA h
      nlinarith [sq_nonneg A])
  exact ⟨z.1, z.2, hzS.1, hzS.2, fun d' δ' hd hδ => hz (d', δ') ⟨hd, hδ⟩⟩

end TsengT4Aux

namespace TsengC4Aux
open TsengCGD.Global TsengCGD.ErrorBound

/-- The slope of `f` along `w` at a point of differentiability tends to `⟪∇f x, w⟫`. -/
theorem slope_tendsto {n : ℕ} {f : Vec n → ℝ} {x : Vec n} (hf : DifferentiableAt ℝ f x)
    (w : Vec n) :
    Tendsto (fun t : ℝ => (f (x + t • w) - f x) / t) (𝓝[>] 0) (𝓝 ⟪gradient f x, w⟫) := by
  have hg : HasFDerivAt f (fderiv ℝ f x) x := hf.hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
  have hc : HasDerivAt (fun t : ℝ => f (x + t • w)) (fderiv ℝ f x w) 0 := by
    have hg' : HasFDerivAt f (fderiv ℝ f x) (x + (0:ℝ) • w) := by simpa using hg
    have := hg'.comp_hasDerivAt (0 : ℝ) hl
    simpa [Function.comp_def] using this
  have hfd : fderiv ℝ f x w = ⟪gradient f x, w⟫ := by
    simp [gradient]
  rw [hasDerivAt_iff_tendsto_slope_zero] at hc
  have := hc.mono_left (nhdsWithin_mono _ (fun t (ht : t ∈ Set.Ioi (0:ℝ)) => by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt ht))
  rw [hfd] at this
  refine this.congr' ?_
  filter_upwards with t
  simp [smul_eq_mul, div_eq_inv_mul]


/-- First-order lower bound for a strongly convex differentiable function. -/
theorem sc_lower {n : ℕ} {f : Vec n → ℝ} {D : Set (Vec n)} {μ : ℝ} (hsc : StrongConvexOn D μ f)
    {x y : Vec n} (hx : x ∈ D) (hy : y ∈ D) (hf : DifferentiableAt ℝ f x) :
    f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  have hT := slope_tendsto hf (y - x)
  have hR : Tendsto (fun t : ℝ => f y - f x - (1 - t) * (μ / 2 * ‖x - y‖ ^ 2)) (𝓝[>] 0)
      (𝓝 (f y - f x - (1 - 0) * (μ / 2 * ‖x - y‖ ^ 2))) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact ((continuous_const.sub continuous_const).sub
      ((continuous_const.sub continuous_id).mul continuous_const)).tendsto 0
  have hle := le_of_tendsto_of_tendsto hT hR (by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h := hsc.2 hx hy (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (by ring : (1 - t) + t = 1)
    have heq : (1 - t) • x + t • y = x + t • (y - x) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [heq, smul_eq_mul, smul_eq_mul] at h
    rw [div_le_iff₀ ht0]
    nlinarith)
  rw [norm_sub_rev] at hle
  linarith

open Classical in
/-- A convex `P` with lower semicontinuous extension is bounded below by an affine function of
`‖y - x0‖`. -/
theorem lin_lower {n : ℕ} {D : Set (Vec n)} {P : Vec n → ℝ} (hP : ConvexOn ℝ D P)
    (hlsc : LowerSemicontinuous (fun x => if x ∈ D then (P x : EReal) else ⊤))
    {x0 : Vec n} (hx0 : x0 ∈ D) :
    ∃ b, 0 ≤ b ∧ ∀ y ∈ D, P x0 - b * (1 + ‖y - x0‖) ≤ P y := by
  obtain ⟨z, hzB, hzmin⟩ := (hlsc.lowerSemicontinuousOn (Metric.closedBall x0 1)).exists_isMinOn
    ⟨x0, Metric.mem_closedBall_self zero_le_one⟩ (isCompact_closedBall x0 1)
  have hz0 := isMinOn_iff.1 hzmin x0 (Metric.mem_closedBall_self zero_le_one)
  simp only [hx0, if_true] at hz0
  have hzD : z ∈ D := by
    by_contra hzD
    simp [hzD] at hz0
  simp only [hzD, if_true, EReal.coe_le_coe_iff] at hz0
  have hball : ∀ y ∈ D, ‖y - x0‖ ≤ 1 → P z ≤ P y := by
    intro y hy hr
    have := isMinOn_iff.1 hzmin y (show y ∈ Metric.closedBall x0 1 by rwa [Metric.mem_closedBall, dist_eq_norm])
    simpa [hy, hzD] using this
  refine ⟨P x0 - P z, by linarith, fun y hy => ?_⟩
  by_cases hr : ‖y - x0‖ ≤ 1
  · have := hball y hy hr
    nlinarith [norm_nonneg (y - x0)]
  · push Not at hr
    set r := ‖y - x0‖ with hrdef
    have hr0 : 0 < r := by linarith
    set s := 1 / r
    have hs0 : 0 < s := by positivity
    have hs1 : s < 1 := by rw [div_lt_one hr0]; exact hr
    have hsr : s * r = 1 := by simp only [s]; field_simp
    have hz' : (1 - s) • x0 + s • y ∈ D := hP.1 hx0 hy (by linarith) hs0.le (by ring)
    have hnorm : ‖(1 - s) • x0 + s • y - x0‖ ≤ 1 := by
      have : (1 - s) • x0 + s • y - x0 = s • (y - x0) := by
        rw [smul_sub, sub_smul, one_smul]; abel
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hs0, ← hrdef, hsr]
    have h1 := hball _ hz' hnorm
    have h2 := hP.2 hx0 hy (show (0:ℝ) ≤ 1 - s by linarith) hs0.le (by ring : (1 - s) + s = 1)
    simp only [smul_eq_mul] at h2
    have h3 : P z ≤ (1 - s) * P x0 + s * P y := h1.trans h2
    have h4 : r * P z ≤ r * ((1 - s) * P x0 + s * P y) := mul_le_mul_of_nonneg_left h3 hr0.le
    have h5 : r * ((1 - s) * P x0 + s * P y) = r * P x0 - P x0 + P y := by
      have : r * s = 1 := by rw [mul_comm]; exact hsr
      linear_combination (P y - P x0) * this
    nlinarith

open Classical in
theorem isClosed_epi {n : ℕ} {D : Set (Vec n)} {P : Vec n → ℝ}
    (h : LowerSemicontinuous (fun x => if x ∈ D then (P x : EReal) else ⊤)) :
    IsClosed {p : Vec n × ℝ | p.1 ∈ D ∧ P p.1 ≤ p.2} := by
  have hE := h.isClosed_epigraph
  have hc : Continuous (fun p : Vec n × ℝ => (p.1, ((p.2 : ℝ) : EReal))) :=
    continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
  convert hE.preimage hc using 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  by_cases hp : p.1 ∈ D
  · simp [hp]
  · simp [hp]

open Classical in
/-- Existence of a minimizer of `q + cP` over `D` for `q` continuous on `D` with a quadratic
lower bound. -/
theorem exists_min {n : ℕ} {D : Set (Vec n)} {P : Vec n → ℝ} {c : ℝ} (hc : 0 < c)
    (hP : ConvexOn ℝ D P)
    (hlsc : LowerSemicontinuous (fun x => if x ∈ D then (P x : EReal) else ⊤))
    {x0 : Vec n} (hx0 : x0 ∈ D) {q : Vec n → ℝ} (hq : ContinuousOn q D) {α0 μ : ℝ} {v : Vec n}
    (hμ : 0 < μ) (hqb : ∀ y ∈ D, α0 + ⟪v, y - x0⟫ + μ / 2 * ‖y - x0‖ ^ 2 ≤ q y) :
    ∃ z ∈ D, ∀ y ∈ D, q z + c * P z ≤ q y + c * P y := by
  obtain ⟨b, hb0, hb⟩ := lin_lower hP hlsc hx0
  set M := q x0 + c * P x0
  set A0 := α0 + c * (P x0 - b)
  set B0 := ‖v‖ + c * b
  set K := |M - A0| + 1
  set r0 := 2 * (B0 + K) / μ + 1
  set Q0 := α0 - ‖v‖ ^ 2 / (2 * μ)
  set T := |M - Q0| / c + |P x0|
  have hB0 : 0 ≤ B0 := by positivity
  have hK : 1 ≤ K := by have := abs_nonneg (M - A0); linarith
  have hr0 : 1 ≤ r0 := by have : 0 ≤ 2 * (B0 + K) / μ := by positivity
                          linarith
  -- lower bounds
  have hqv : ∀ y ∈ D, α0 - ‖v‖ * ‖y - x0‖ + μ / 2 * ‖y - x0‖ ^ 2 ≤ q y := by
    intro y hy
    have := hqb y hy
    have := real_inner_le_norm v (y - x0)
    have := neg_le_of_abs_le (abs_real_inner_le_norm v (y - x0))
    linarith
  have hQ0 : ∀ y ∈ D, Q0 ≤ q y := by
    intro y hy
    have h1 := hqv y hy
    have h2 : 0 ≤ (μ * ‖y - x0‖ - ‖v‖) ^ 2 / (2 * μ) := by positivity
    have h3 : (μ * ‖y - x0‖ - ‖v‖) ^ 2 / (2 * μ) =
        μ / 2 * ‖y - x0‖ ^ 2 - ‖v‖ * ‖y - x0‖ + ‖v‖ ^ 2 / (2 * μ) := by
      field_simp; ring
    simp only [Q0]; linarith
  have hfar : ∀ y ∈ D, r0 < ‖y - x0‖ → M ≤ q y + c * P y := by
    intro y hy hr
    set r := ‖y - x0‖
    have h1 := hqv y hy
    have h2 := hb y hy
    have h2' : c * (P x0 - b * (1 + r)) ≤ c * P y := mul_le_mul_of_nonneg_left h2 hc.le
    -- h(r) = A0 - B0 r + μ/2 r^2
    have hrK : 2 * (B0 + K) / μ ≤ r := by linarith
    have hrK' : 2 * (B0 + K) ≤ μ * r := by
      rw [div_le_iff₀ hμ] at hrK; linarith
    have hr1 : 1 ≤ r := by linarith
    have h3 : K * r ≤ μ / 2 * r ^ 2 - B0 * r := by nlinarith
    have h4 : M - A0 ≤ K := by have := le_abs_self (M - A0); linarith
    have h5 : K ≤ K * r := by nlinarith
    have : A0 - B0 * r + μ / 2 * r ^ 2 ≤ q y + c * P y := by
      simp only [A0, B0]; nlinarith
    linarith
  have hhigh : ∀ y ∈ D, ∀ t, T < t → M ≤ q y + c * t := by
    intro y hy t ht
    have h1 := hQ0 y hy
    have h2 : |M - Q0| ≤ c * t := by
      have : |M - Q0| / c < t := by have := abs_nonneg (P x0); simp only [T] at ht; linarith
      rw [div_lt_iff₀ hc] at this; linarith
    have := le_abs_self (M - Q0)
    linarith
  -- the compact set
  set Kc : Set (Vec n × ℝ) :=
    {p | p.1 ∈ D ∧ P p.1 ≤ p.2} ∩ ({p | ‖p.1 - x0‖ ≤ r0} ∩ {p | p.2 ≤ T}) with hKc
  have hKcl : IsClosed Kc := by
    refine (isClosed_epi hlsc).inter (IsClosed.inter ?_ ?_)
    · exact isClosed_le (by fun_prop) continuous_const
    · exact isClosed_le continuous_snd continuous_const
  have hKb : Bornology.IsBounded Kc := by
    refine ((Metric.isBounded_closedBall (x := x0) (r := r0)).prod
      (Metric.isBounded_Icc (P x0 - b * (1 + r0)) T)).subset ?_
    rintro ⟨y, t⟩ ⟨⟨hy, hPt⟩, hr, hT⟩
    simp only [Set.mem_ofPred_eq] at hr hT
    refine ⟨by rwa [Metric.mem_closedBall, dist_eq_norm], ?_, hT⟩
    have := hb y hy
    have : b * (1 + ‖y - x0‖) ≤ b * (1 + r0) := by
      apply mul_le_mul_of_nonneg_left _ hb0; linarith
    simp only at hPt ⊢
    linarith
  have hKcomp : IsCompact Kc := Metric.isCompact_of_isClosed_isBounded hKcl hKb
  have hx0K : (x0, P x0) ∈ Kc := by
    refine ⟨⟨hx0, le_rfl⟩, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, sub_self, norm_zero]; linarith
    · simp only [Set.mem_ofPred_eq, T]
      have := le_abs_self (P x0); have := div_nonneg (abs_nonneg (M - Q0)) hc.le; linarith
  have hφc : ContinuousOn (fun p : Vec n × ℝ => q p.1 + c * p.2) Kc := by
    refine ContinuousOn.add ?_ (continuous_const.mul continuous_snd).continuousOn
    exact hq.comp continuous_fst.continuousOn (fun p hp => hp.1.1)
  obtain ⟨z, hzK, hzmin⟩ := hKcomp.exists_isMinOn ⟨_, hx0K⟩ hφc
  have hzle : ∀ p ∈ Kc, q z.1 + c * z.2 ≤ q p.1 + c * p.2 := fun p hp => isMinOn_iff.1 hzmin p hp
  have hzM : q z.1 + c * z.2 ≤ M := hzle _ hx0K
  refine ⟨z.1, hzK.1.1, fun y hy => ?_⟩
  have hz1 : q z.1 + c * P z.1 ≤ q z.1 + c * z.2 := by
    have := mul_le_mul_of_nonneg_left hzK.1.2 hc.le; linarith
  refine hz1.trans ?_
  by_cases hr : ‖y - x0‖ ≤ r0
  · by_cases hT : P y ≤ T
    · exact hzle (y, P y) ⟨⟨hy, le_rfl⟩, hr, hT⟩
    · push Not at hT
      exact hzM.trans (hhigh y hy _ hT)
  · push Not at hr
    exact hzM.trans (hfar y hy hr)

theorem qf_one {n : ℕ} (d : Vec n) : qf 1 d = ‖d‖ ^ 2 := by
  rw [qf, Matrix.one_mulVec, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [dotProduct, sq]

/-- `⟪g + d, d⟫ + cP(x+d) ≤ ⟪g + d, y - x⟫ + cP(y)` for the direction `d` of (6) with `H = I`. -/
theorem fermat {n : ℕ} {f : Vec n → ℝ} {D : Set (Vec n)} {P : Vec n → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hP : ConvexOn ℝ D P) {x d : Vec n} (hd : IsDir f D P c 1 x Finset.univ d)
    {y : Vec n} (hy : y ∈ D) :
    ⟪gradient f x + d, d⟫ + c * P (x + d) ≤ ⟪gradient f x + d, y - x⟫ + c * P y := by
  obtain ⟨_, hxd, hmin⟩ := hd
  set g := gradient f x
  set w := y - x - d
  set X := ⟪g, w⟫ + ⟪d, w⟫ + c * (P y - P (x + d))
  have hX : 0 ≤ X := by
    have hT : Tendsto (fun t : ℝ => X + t * (‖w‖ ^ 2 / 2)) (𝓝[>] 0) (𝓝 (X + 0 * (‖w‖ ^ 2 / 2))) :=
      ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0).mono_left
        nhdsWithin_le_nhds
    rw [zero_mul, add_zero] at hT
    refine ge_of_tendsto hT ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have heq : x + (d + t • w) = (1 - t) • (x + d) + t • y := by
      simp only [w, smul_sub, sub_smul, one_smul, smul_add]; abel
    have hmem : x + (d + t • w) ∈ D := by
      rw [heq]; exact hP.1 hxd hy (by linarith) ht0.le (by ring)
    have h1 := hmin (d + t • w) (fun j hj => absurd (Finset.mem_univ j) hj) hmem
    unfold subObj at h1
    rw [qf_one, qf_one] at h1
    have h2 := hP.2 hxd hy (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (by ring : (1 - t) + t = 1)
    rw [← heq, smul_eq_mul, smul_eq_mul] at h2
    rw [inner_add_right, inner_smul_right, norm_add_sq_real, norm_smul, inner_smul_right,
      Real.norm_eq_abs, abs_of_pos ht0] at h1
    have h3 : c * P (x + (d + t • w)) ≤ c * ((1 - t) * P (x + d) + t * P y) :=
      mul_le_mul_of_nonneg_left h2 hc
    have h4 : 0 ≤ t * X + t * (t * (‖w‖ ^ 2 / 2)) := by simp only [X]; nlinarith
    have h5 : 0 ≤ t * (X + t * (‖w‖ ^ 2 / 2)) := by linarith
    exact nonneg_of_mul_nonneg_right (by linarith) ht0
  have e1 : ⟪g + d, y - x⟫ = ⟪g + d, w⟫ + ⟪g + d, d⟫ := by
    rw [← inner_add_right]; congr 1; simp only [w]; abel
  rw [e1]
  simp only [inner_add_left]
  simp only [X] at hX
  linarith

end TsengC4Aux

open TsengCGD.Global TsengCGD.ErrorBound TsengC4Aux in
theorem caseC4 {n : ℕ} (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
    (hs : TsengCGD.Global.Standing f D P c) (hC : C4 f D) :
    TsengCGD.Linear.Assumption2a f D P c := by
  have hc := hs.c_pos
  obtain ⟨⟨x0, hx0⟩, _, hPc, hlsc⟩ := hs.properConvexLsc
  obtain ⟨U, hU, hDU, hfU⟩ := hs.smooth
  obtain ⟨⟨μ, hμ, hsc⟩, L, hL0, hL⟩ := hC
  have hdiff : ∀ x ∈ D, DifferentiableAt ℝ f x := fun x hx =>
    ((hfU.differentiableOn (by norm_num)) x (hDU hx)).differentiableAt (hU.mem_nhds (hDU hx))
  have hcont : ContinuousOn f D := hfU.continuousOn.mono hDU
  -- a minimizer of F_c over dom P
  obtain ⟨xb, hxb, hmin⟩ := exists_min hc hPc hlsc hx0 hcont (α0 := f x0)
    (v := gradient f x0) hμ (fun y hy => sc_lower hsc hx0 hy (hdiff x0 hx0))
  have hstat : xb ∈ TsengCGD.Linear.statSet f D P c := by
    refine ⟨hxb, fun d ε hε => ?_⟩
    filter_upwards [self_mem_nhdsWithin] with α (hα : 0 < α) hmem
    have := hmin _ hmem
    have : 0 ≤ (TsengCGD.Global.Fc f P c (xb + α • d) - TsengCGD.Global.Fc f P c xb) / α := by
      apply div_nonneg _ hα.le
      simp only [TsengCGD.Global.Fc]; linarith
    linarith
  -- the stationarity inequality at xb
  have hsi : ∀ y ∈ D, c * P xb ≤ ⟪gradient f xb, y - xb⟫ + c * P y := by
    intro y hy
    have hT := slope_tendsto (hdiff xb hxb) (y - xb)
    have := ge_of_tendsto hT (show ∀ᶠ t in 𝓝[>] (0:ℝ),
        c * (P xb - P y) ≤ (f (xb + t • (y - xb)) - f xb) / t by
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
      obtain ⟨ht0, ht1⟩ := ht
      have heq : xb + t • (y - xb) = (1 - t) • xb + t • y := by
        rw [smul_sub, sub_smul, one_smul]; abel
      have hmem : xb + t • (y - xb) ∈ D := by
        rw [heq]; exact hPc.1 hxb hy (by linarith) ht0.le (by ring)
      have h1 := hmin _ hmem
      have h2 := hPc.2 hxb hy (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (by ring : (1 - t) + t = 1)
      rw [← heq, smul_eq_mul, smul_eq_mul] at h2
      have h3 := mul_le_mul_of_nonneg_left h2 hc.le
      rw [le_div_iff₀ ht0]
      nlinarith)
    linarith
  -- the direction d_I(x) exists
  have hdir : ∀ x ∈ D, IsDir f D P c 1 x Finset.univ (dI f D P c x) := by
    intro x hx
    obtain ⟨ys, hys, hysmin⟩ := exists_min hc hPc hlsc hx
      (q := fun y => ⟪gradient f x, y - x⟫ + ‖y - x‖ ^ 2 / 2)
      (by fun_prop) (α0 := 0) (v := gradient f x) one_pos (fun y _ => by linarith)
    have hex : ∃ d, IsDir f D P c 1 x Finset.univ d := by
      refine ⟨ys - x, fun j hj => absurd (Finset.mem_univ j) hj, by simpa using hys, ?_⟩
      intro d' _ hd'
      unfold subObj
      rw [qf_one, qf_one]
      have := hysmin (x + d') hd'
      simp only [add_sub_cancel_left] at this
      rw [add_sub_cancel]
      exact this
    exact Classical.epsilon_spec hex
  refine ⟨⟨xb, hstat⟩, fun ζ => ⟨(L + 1) / μ, by positivity, 1, one_pos, fun x hx _ _ => ?_⟩⟩
  set d := dI f D P c x
  set g := gradient f x
  set gb := gradient f xb
  have hxd : x + d ∈ D := (hdir x hx).2.1
  have F1 := fermat hc.le hPc (hdir x hx) hxb
  have F2 := hsi (x + d) hxd
  have M1 := sc_lower hsc hx hxb (hdiff x hx)
  have M2 := sc_lower hsc hxb hx (hdiff xb hxb)
  have hLip : ⟪gb - g, d⟫ ≤ L * ‖x - xb‖ * ‖d‖ := by
    refine (real_inner_le_norm _ _).trans ?_
    have := hL xb hxb x hx
    rw [norm_sub_rev xb x] at this
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have hCS : ⟪d, xb - x⟫ ≤ ‖d‖ * ‖x - xb‖ := by
    rw [norm_sub_rev x xb]; exact real_inner_le_norm _ _
  set e := ‖x - xb‖ with he
  have hn1 : ‖xb - x‖ = e := norm_sub_rev _ _
  rw [hn1] at M1
  have hdd : ⟪d, d⟫ = ‖d‖ ^ 2 := real_inner_self_eq_norm_sq d
  have i1 : ⟪g + d, d⟫ = ⟪g, d⟫ + ⟪d, d⟫ := inner_add_left _ _ _
  have i2 : ⟪g + d, xb - x⟫ = ⟪g, xb - x⟫ + ⟪d, xb - x⟫ := inner_add_left _ _ _
  have i3 : ⟪gb, x + d - xb⟫ = ⟪gb, x - xb⟫ + ⟪gb, d⟫ := by
    rw [← inner_add_right]; congr 1; abel
  have i4 : ⟪gb - g, d⟫ = ⟪gb, d⟫ - ⟪g, d⟫ := inner_sub_left _ _ _
  have key : μ * e ^ 2 ≤ (L + 1) * e * ‖d‖ := by
    nlinarith [sq_nonneg ‖d‖]
  have he0 : 0 ≤ e := norm_nonneg _
  have hfin : e ≤ (L + 1) / μ * ‖d‖ := by
    rcases he0.lt_or_eq with hpos | hzero
    · have : μ * e ≤ (L + 1) * ‖d‖ := by nlinarith
      rw [div_mul_eq_mul_div, le_div_iff₀ hμ]; linarith
    · rw [← hzero]; positivity
  calc Metric.infDist x (TsengCGD.Linear.statSet f D P c) ≤ dist x xb :=
        Metric.infDist_le_dist_of_mem hstat
    _ = e := dist_eq_norm _ _
    _ ≤ (L + 1) / μ * ‖d‖ := hfin

open TsengCGD.ErrorBound in
theorem solution {n : ℕ} (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
    (hs : TsengCGD.Global.Standing f D P c)
    (hC : ((TsengCGD.Linear.statSet f D P c).Nonempty ∧ (C1 f D P ∨ C2 f D P ∨ C3 f D P)) ∨ C4 f D) :
    TsengCGD.Linear.Assumption2a f D P c := by
  rcases hC with ⟨hX, hC⟩ | hC4
  · -- P polyhedral, hence Lipschitz on dom P
    have hpoly : IsPolyhedral D P := by
      rcases hC with h | h | h
      · exact h.2
      · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h⟩ := h; exact h
      · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := h; exact h
    obtain ⟨K, hK⟩ := TsengT4Aux.polyhedral_lip hpoly
    obtain ⟨κ, hκ, h6⟩ := lemma6 K hK.1
    refine ⟨hX, fun ζ => ?_⟩
    obtain ⟨τ', hτ', ε', hε', h7⟩ := lemma7 f D P c hs hX hC ζ
    refine ⟨τ' * κ, mul_pos hτ' hκ, ε' / κ, div_pos hε' hκ, fun x hx hF hdI => ?_⟩
    obtain ⟨dt, δt, hsol⟩ := TsengT4Aux.exists_epiSubSol hs hx
    have hb := h6 f D P c hs hK x hx dt δt hsol
    have hb' : pairNorm dt δt ≤ ε' := by
      calc pairNorm dt δt ≤ κ * ‖TsengCGD.Global.dI f D P c x‖ := hb
        _ ≤ κ * (ε' / κ) := mul_le_mul_of_nonneg_left hdI hκ.le
        _ = ε' := by field_simp
    calc Metric.infDist x (TsengCGD.Linear.statSet f D P c) ≤ τ' * pairNorm dt δt :=
          h7 x hx hF dt δt hsol hb'
      _ ≤ τ' * (κ * ‖TsengCGD.Global.dI f D P c x‖) := mul_le_mul_of_nonneg_left hb hτ'.le
      _ = τ' * κ * ‖TsengCGD.Global.dI f D P c x‖ := by ring
  · exact caseC4 f D P c hs hC4
