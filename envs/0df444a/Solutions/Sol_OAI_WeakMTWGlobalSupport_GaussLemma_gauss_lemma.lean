-- Prove2me | solution 1 for OAI.WeakMTWGlobalSupport.GaussLemma.gauss_lemma
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T03:00:57.126091+00:00
-- url     : https://prove2.me/submissions/6b998234-2973-4009-b1c3-a3b4dc4a1810

import Mathlib
import Definitions.Def_OAIQWMTW000

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_InitialScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace GeodesicScaling
open Set Filter CoordinateGeometry
open scoped Topology ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E]

theorem rescale_flow {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {U : Set (ℝ × (E × E))} {Φ : ℝ × (E × E) → E × E}
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
    (hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t, q.2)) (geodesicSpray G (Φ q)) q.1)
    {q : E × E} {T s : ℝ} (hT : 0 ≤ T)
    (hseg₁ : ∀ t ∈ Icc (0 : ℝ) T, (t, scalePhase s q) ∈ U)
    (hseg₂ : ∀ t ∈ Icc (0 : ℝ) T, (s * t, q) ∈ U) :
    ∀ t ∈ Icc (0 : ℝ) T, Φ (t, scalePhase s q) = scalePhase s (Φ (s * t, q)) := by
  let u : ℝ → E × E := fun t => Φ (t, scalePhase s q)
  let v : ℝ → E × E := fun t => scalePhase s (Φ (s * t, q))
  have hdu : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt u (geodesicSpray G (u t)) t :=
    fun t ht => (hode _ (hseg₁ t ht)).2
  have hdv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt v (geodesicSpray G (v t)) t := by
    intro t ht
    have hd := (hode _ (hseg₂ t ht)).2.scomp t ((hasDerivAt_id t).const_mul s)
    have he := (scalePhase s).hasFDerivAt.comp_hasDerivAt t hd
    convert! he using 1
    simp only [mul_one, scale_spray, v]
  have hmem : ∀ t ∈ Icc (0 : ℝ) T, (u t).1 ∈ S ∧ (v t).1 ∈ S := by
    intro t ht
    exact ⟨(hode _ (hseg₁ t ht)).1, (hode _ (hseg₂ t ht)).1⟩
  have hf : ∀ z ∈ u '' Icc (0 : ℝ) T ∪ v '' Icc (0 : ℝ) T,
      ContDiffAt ℝ 1 (geodesicSpray G) z := by
    intro z hz
    have hzS : z.1 ∈ S := by
      rcases hz with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
      · exact (hmem t ht).1
      · exact (hmem t ht).2
    exact (((contDiffOn_geodesicSpray hS hG hpos) z ⟨hzS, mem_univ _⟩).contDiffAt
      ((hS.prod isOpen_univ).mem_nhds ⟨hzS, mem_univ _⟩)).of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top)
  have h0 : u 0 = v 0 := by
    simp only [u, v, mul_zero, hzero _ (hseg₁ 0 ⟨le_rfl, hT⟩)]
    rw [hzero q (by simpa using hseg₂ 0 ⟨le_rfl, hT⟩)]
  exact fun t ht => FlowLinearization.unique_Icc
    (fun r hr => (hdu r hr).continuousAt.continuousWithinAt)
    (fun r hr => (hdv r hr).continuousAt.continuousWithinAt) hf
    (fun r hr => (hdu r hr).hasDerivWithinAt) (fun r hr => (hdv r hr).hasDerivWithinAt) h0 ht

theorem radial_variation {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {U : Set (ℝ × (E × E))} {Φ : ℝ × (E × E) → E × E}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
    (hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t, q.2)) (geodesicSpray G (Φ q)) q.1)
    {q : E × E} {T : ℝ} (hT : 0 ≤ T)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, (t, q) ∈ U) :
    (fderiv ℝ Φ (T, q) (0, (0, q.2))).1 = T • (Φ (T, q)).2 := by
  have hneigh : ∀ᶠ s in 𝓝 (1 : ℝ), ∀ t ∈ Icc (0 : ℝ) T,
      (t, scalePhase s q) ∈ U ∧ (s * t, q) ∈ U := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hA : Continuous (fun z : ℝ × ℝ => (z.2, scalePhase z.1 q)) := by
      exact continuous_snd.prodMk (continuous_const.prodMk (continuous_fst.smul continuous_const))
    have hB : Continuous (fun z : ℝ × ℝ => (z.1 * z.2, q)) :=
      (continuous_fst.mul continuous_snd).prodMk continuous_const
    have hmem : (t, q) ∈ U := hseg t ht
    have h₁ := (hA.continuousAt (x := (1, t))).preimage_mem_nhds
      (t := U) (by simpa using hU.mem_nhds hmem)
    have h₂ := (hB.continuousAt (x := (1, t))).preimage_mem_nhds
      (t := U) (by simpa using hU.mem_nhds hmem)
    exact Filter.inter_mem h₁ h₂
  have heq : (fun s => (Φ (T, scalePhase s q)).1) =ᶠ[𝓝 (1 : ℝ)]
      (fun s => (Φ (s * T, q)).1) := by
    filter_upwards [hneigh] with s hs
    have he := rescale_flow hS hG hpos hzero hode hT (fun t ht => (hs t ht).1)
      (fun t ht => (hs t ht).2) T ⟨hT, le_rfl⟩
    simpa only [scalePhase_apply] using congrArg Prod.fst he
  have hpath : HasDerivAt (fun s : ℝ => (T, scalePhase s q)) (0, (0, q.2)) 1 := by
    convert! (hasDerivAt_const (1 : ℝ) T).prodMk
      ((hasDerivAt_const (1 : ℝ) q.1).prodMk ((hasDerivAt_id (1 : ℝ)).smul_const q.2)) using 1
    simp
  have hTx := hseg T ⟨hT, le_rfl⟩
  have hdΦ := (((hΦ _ hTx).contDiffAt (hU.mem_nhds hTx)).differentiableAt (by simp)).hasFDerivAt
  have hdΦ' : HasFDerivAt Φ (fderiv ℝ Φ (T, q)) (T, scalePhase 1 q) := by
    simpa using hdΦ
  have hdL0 := hdΦ'.comp_hasDerivAt (1 : ℝ) hpath
  have hdL : HasDerivAt (fun s => (Φ (T, scalePhase s q)).1)
      (fderiv ℝ Φ (T, q) (0, (0, q.2))).1 1 := by
    convert! hdL0.fst using 1
  have hdPos : HasDerivAt (fun t => (Φ (t, q)).1) (Φ (T, q)).2 T :=
    (hode _ hTx).2.fst
  have hdPos' : HasDerivAt (fun t => (Φ (t, q)).1) (Φ (T, q)).2 (1 * T) := by
    simpa using hdPos
  have hdR := hdPos'.scomp (1 : ℝ) ((hasDerivAt_id (1 : ℝ)).mul_const T)
  simpa only [one_mul, one_smul] using hdL.unique (hdR.congr_of_eventuallyEq heq)

end
end GeodesicScaling

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_CurveVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace VariationCalculus
open Set Filter
open scoped Topology ContDiff
variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem parameter_variation_hasDerivAt {Φ Ψ : ℝ × P → F} {U : Set (ℝ × P)}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ 2 Φ U)
    (htime : ∀ q ∈ U, HasDerivAt (fun t => Φ (t, q.2)) (Ψ q) q.1)
    {T : ℝ} {x w : P} (hTx : (T, x) ∈ U)
    (hΨ : DifferentiableAt ℝ Ψ (T, x)) :
    HasDerivAt (fun t => fderiv ℝ Φ (t, x) (0, w))
      (fderiv ℝ Ψ (T, x) (0, w)) T := by
  have hc := (hΦ (T, x) hTx).contDiffAt (hU.mem_nhds hTx)
  have hdD : DifferentiableAt ℝ (fderiv ℝ Φ) (T, x) :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA := hdD.hasFDerivAt.clm_apply (hasFDerivAt_const (1, 0) (T, x))
  have heq : (fun q => fderiv ℝ Φ q (1, 0)) =ᶠ[𝓝 (T, x)] Ψ := by
    filter_upwards [hU.mem_nhds hTx] with q hq
    exact (hasDerivAt_time_slice (((hΦ q hq).contDiffAt (hU.mem_nhds hq)).differentiableAt
      (by norm_num))).unique (htime q hq)
  have he := congrArg (fun L : (ℝ × P) →L[ℝ] F => L (0, w))
    (hA.unique (hΨ.hasFDerivAt.congr_of_eventuallyEq heq))
  have hs := hc.isSymmSndFDerivAt (by simp) (1, 0) (0, w)
  have hd := ((hasDerivAt_time_slice hdD).hasFDerivAt.clm_apply (hasFDerivAt_const (0, w) T)).hasDerivAt
  convert! hd using 1
  simpa [hs] using he.symm

end VariationCalculus

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_FirstVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace FirstVariation
open Set Filter CoordinateGeometry
open scoped Topology ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem geodesic_pairing_hasDerivAt {G : E → MetricTensor E}
    {c V J : ℝ → E} {t : ℝ} {W : E}
    (hG : DifferentiableAt ℝ G (c t))
    (hpos : ∀ v : E, v ≠ 0 → 0 < G (c t) v v)
    (hc : HasDerivAt c (V t) t)
    (hV : HasDerivAt V (-christoffel G (c t) (V t) (V t)) t)
    (hJ : HasDerivAt J W t) :
    HasDerivAt (fun r => G (c r) (V r) (J r))
      (fderiv ℝ G (c t) (J t) (V t) (V t) / 2 + G (c t) (V t) W) t := by
  have hd := hasDerivAt_metric_pairing hG hc hV hJ
  have hm := metric_christoffel hpos (V t) (V t) (J t)
  convert! hd using 1
  simp only [map_neg, neg_apply]
  linarith

omit [FiniteDimensional ℝ E] in
theorem parameter_hasDerivAt {c : ℝ × ℝ → E} {t s : ℝ}
    (hc : DifferentiableAt ℝ c (t, s)) :
    HasDerivAt (fun r => c (t, r)) (fderiv ℝ c (t, s) (0, 1)) s := by
  convert! hc.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_const s t).prodMk (hasDerivAt_id s)) using 1

theorem geodesic_fan_pairing {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {c V : ℝ × ℝ → E} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hc : ContDiffOn ℝ 2 c U) (hV : ContDiffOn ℝ 1 V U)
    (hmem : ∀ q ∈ U, c q ∈ S)
    (hct : ∀ q ∈ U, HasDerivAt (fun t => c (t, q.2)) (V q) q.1)
    (hVt : ∀ q ∈ U, HasDerivAt (fun t => V (t, q.2))
      (-christoffel G (c q) (V q) (V q)) q.1)
    {T : ℝ} (hT : 0 ≤ T) {P : Set ℝ} (hP : P ∈ 𝓝 (0 : ℝ))
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ P, (t, s) ∈ U)
    {x v w : E} (hc0 : ∀ s ∈ P, c (0, s) = x)
    (hV0 : ∀ s ∈ P, V (0, s) = v + s • w) :
    ∀ t ∈ Icc (0 : ℝ) T,
      G (c (t, 0)) (V (t, 0)) (fderiv ℝ c (t, 0) (0, 1)) = t * G x v w := by
  have hP0 : (0 : ℝ) ∈ P := mem_of_mem_nhds hP
  have h00 : (0, (0 : ℝ)) ∈ U := hseg 0 ⟨le_rfl, hT⟩ 0 hP0
  have hx : x ∈ S := by simpa only [hc0 0 hP0] using hmem _ h00
  let J : ℝ → E := fun t => fderiv ℝ c (t, 0) (0, 1)
  let W : ℝ → E := fun t => fderiv ℝ V (t, 0) (0, 1)
  have hq : ∀ t ∈ Icc (0 : ℝ) T, (t, (0 : ℝ)) ∈ U := fun t ht => hseg t ht 0 hP0
  have hCdiff : ∀ t ∈ Icc (0 : ℝ) T, DifferentiableAt ℝ c (t, 0) :=
    fun t ht => ((hc _ (hq t ht)).contDiffAt (hU.mem_nhds (hq t ht))).differentiableAt (by norm_num)
  have hVdiff : ∀ t ∈ Icc (0 : ℝ) T, DifferentiableAt ℝ V (t, 0) :=
    fun t ht => ((hV _ (hq t ht)).contDiffAt (hU.mem_nhds (hq t ht))).differentiableAt (by norm_num)
  have hdJ : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt J (W t) t := by
    intro t ht
    exact VariationCalculus.parameter_variation_hasDerivAt hU hc hct (hq t ht) (hVdiff t ht)
  have henergy : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ P,
      G (c (t, s)) (V (t, s)) (V (t, s)) = G x (v + s • w) (v + s • w) := by
    intro t ht s hs
    have he := geodesic_energy_constant hS hG hsym hpos
      (fun r hr => hmem _ (hseg r hr s hs))
      (fun r hr => hct _ (hseg r hr s hs)) (fun r hr => hVt _ (hseg r hr s hs)) t ht
    simpa only [hc0 s hs, hV0 s hs] using he
  have henergyD : ∀ t ∈ Icc (0 : ℝ) T,
      fderiv ℝ G (c (t, 0)) (J t) (V (t, 0)) (V (t, 0)) +
        2 * G (c (t, 0)) (V (t, 0)) (W t) = 2 * G x v w := by
    intro t ht
    have hGs := (hG _ (hmem _ (hq t ht))).differentiableAt (hS.mem_nhds (hmem _ (hq t ht)))
    have hdL := hasDerivAt_metric_pairing hGs
      (parameter_hasDerivAt (hCdiff t ht)) (parameter_hasDerivAt (hVdiff t ht))
      (parameter_hasDerivAt (hVdiff t ht))
    have hdR := hasDerivAt_metric_pairing ((hG x hx).differentiableAt (hS.mem_nhds hx))
      (hasDerivAt_const (0 : ℝ) x)
      (((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v)
      (((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v)
    have heq : (fun s => G (c (t, s)) (V (t, s)) (V (t, s))) =ᶠ[𝓝 (0 : ℝ)]
        (fun s => G x (v + s • w) (v + s • w)) := by
      filter_upwards [hP] with s hs
      exact henergy t ht s hs
    have he := hdL.unique (hdR.congr_of_eventuallyEq heq)
    simp only [id_eq, zero_smul, add_zero, map_zero, zero_apply, zero_add, one_smul] at he
    rw [hsym _ (hmem _ (hq t ht)) (W t) (V (t, 0)), hsym x hx w v] at he
    change fderiv ℝ G (c (t, 0)) (J t) (V (t, 0)) (V (t, 0)) +
      G (c (t, 0)) (V (t, 0)) (W t) + G (c (t, 0)) (V (t, 0)) (W t) =
      G x v w + G x v w at he
    linarith
  have hJ0 : J 0 = 0 := by
    have heq : (fun s => c (0, s)) =ᶠ[𝓝 (0 : ℝ)] (fun _ => x) := by
      filter_upwards [hP] with s hs
      exact hc0 s hs
    exact (parameter_hasDerivAt (hCdiff 0 ⟨le_rfl, hT⟩)).unique
      ((hasDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq heq)
  have hpair : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun r => G (c (r, 0)) (V (r, 0)) (J r)) (G x v w) t := by
    intro t ht
    have hm := hmem _ (hq t ht)
    have hd := geodesic_pairing_hasDerivAt (c := fun r => c (r, 0)) (V := fun r => V (r, 0)) (J := J) ((hG _ hm).differentiableAt (hS.mem_nhds hm))
      (hpos _ hm) (hct _ (hq t ht)) (hVt _ (hq t ht)) (hdJ t ht)
    convert! hd using 1
    linarith [henergyD t ht]
  have hconst := constant_of_has_deriv_right_zero
    (f := fun t => G (c (t, 0)) (V (t, 0)) (J t) - t * G x v w)
    (fun t ht => ((hpair t ht).sub ((hasDerivAt_id t).mul_const (G x v w))).continuousAt.continuousWithinAt)
    (fun t ht => by
      convert! ((hpair t (Ico_subset_Icc_self ht)).sub
        ((hasDerivAt_id t).mul_const (G x v w))).hasDerivWithinAt using 1; simp)
  intro t ht
  have he := hconst t ht
  simp only [hJ0, map_zero, zero_mul, sub_zero] at he
  exact sub_eq_zero.mp he

end
end FirstVariation

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_GaussLemma
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace GaussLemma
open Set Filter CoordinateGeometry
open scoped Topology ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem flow_gauss_proof {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {U : Set (ℝ × (E × E))} {Φ : ℝ × (E × E) → E × E}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
    (hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t, q.2)) (geodesicSpray G (Φ q)) q.1)
    {x v : E} {T : ℝ} (hT : 0 ≤ T)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, (t, (x, v)) ∈ U) (w : E) :
    G (Φ (T, (x, v))).1
      (fderiv ℝ Φ (T, (x, v)) (0, (0, v))).1
      (fderiv ℝ Φ (T, (x, v)) (0, (0, w))).1 = T ^ 2 * G x v w := by
  let χ : ℝ × ℝ → ℝ × (E × E) := fun q => (q.1, (x, v + q.2 • w))
  have hχ : ContDiff ℝ ∞ χ :=
    contDiff_fst.prodMk (contDiff_const.prodMk (contDiff_const.add
      (contDiff_snd.smul contDiff_const)))
  let W : Set (ℝ × ℝ) := χ ⁻¹' U
  have hW : IsOpen W := hU.preimage hχ.continuous
  let c : ℝ × ℝ → E := fun q => (Φ (χ q)).1
  let V : ℝ × ℝ → E := fun q => (Φ (χ q)).2
  have hcomp : ContDiffOn ℝ ∞ (Φ ∘ χ) W :=
    hΦ.comp hχ.contDiffOn (fun _ hq => hq)
  have hc : ContDiffOn ℝ 2 c W := hcomp.fst.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hV : ContDiffOn ℝ 1 V W := hcomp.snd.of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top)
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) T, (t, s) ∈ W := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hm : χ (t, 0) ∈ U := by simpa [χ] using hseg t ht
    have hh := ((hχ.continuous.comp continuous_swap).continuousAt (x := (0, t))).preimage_mem_nhds
      (hU.mem_nhds hm)
    exact hh
  let P : Set ℝ := {s | ∀ t ∈ Icc (0 : ℝ) T, (t, s) ∈ W}
  have hP : P ∈ 𝓝 (0 : ℝ) := hnear
  have hfan := FirstVariation.geodesic_fan_pairing hS
    (hG.differentiableOn (by simp)) hsym hpos hW hc hV
    (fun q hq => (hode (χ q) hq).1)
    (fun q hq => (hode (χ q) hq).2.fst)
    (fun q hq => (hode (χ q) hq).2.snd) hT hP
    (fun t ht s hs => hs t ht)
    (x := x) (v := v) (w := w)
    (fun s hs => congrArg Prod.fst (hzero (x, v + s • w) (hs 0 ⟨le_rfl, hT⟩)))
    (fun s hs => congrArg Prod.snd (hzero (x, v + s • w) (hs 0 ⟨le_rfl, hT⟩)))
    T ⟨hT, le_rfl⟩
  have hterm : (T, (x, v)) ∈ U := hseg T ⟨hT, le_rfl⟩
  have hdΦ := ((hΦ _ hterm).contDiffAt (hU.mem_nhds hterm)).differentiableAt
    (by simp)
  have hdχ : HasFDerivAt χ
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        ((0 : ℝ × ℝ →L[ℝ] E).prod
          ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight w))) (T, 0) := by
    exact (hasFDerivAt_fst (p := (T, (0 : ℝ)))).prodMk
      ((hasFDerivAt_const x (T, (0 : ℝ))).prodMk
        (((hasFDerivAt_snd (p := (T, (0 : ℝ)))).smul_const w).const_add v))
  have hdΦ' : HasFDerivAt Φ (fderiv ℝ Φ (T, (x, v))) (χ (T, 0)) := by
    simpa [χ] using hdΦ.hasFDerivAt
  have hdc : HasFDerivAt c _ (T, (0 : ℝ)) := (hdΦ'.comp (T, (0 : ℝ)) hdχ).fst
  have hdval : fderiv ℝ c (T, 0) (0, 1) =
      (fderiv ℝ Φ (T, (x, v)) (0, (0, w))).1 := by
    rw [hdc.fderiv]
    simp [ContinuousLinearMap.comp_apply]
  have hr := GeodesicScaling.radial_variation hS hG hpos hU hΦ hzero hode hT hseg
  rw [hr, map_smul, smul_apply, smul_eq_mul]
  have hf : G (Φ (T, (x, v))).1 (Φ (T, (x, v))).2
      (fderiv ℝ Φ (T, (x, v)) (0, (0, w))).1 = T * G x v w := by
    simpa only [c, V, χ, zero_smul, add_zero, hdval] using hfan
  rw [hf]
  ring

theorem gauss_lemma_oai {G : E → (E →L[ℝ] E →L[ℝ] ℝ)} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {U : Set (ℝ × (E × E))} {Φ : ℝ × (E × E) → E × E}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
    (hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t, q.2))
        ((Φ q).2, -((G (Φ q).1).inverse ((1 / 2 : ℝ) •
          (fderiv ℝ G (Φ q).1 (Φ q).2 (Φ q).2 + fderiv ℝ G (Φ q).1 (Φ q).2 (Φ q).2 -
            ((fderiv ℝ G (Φ q).1).flip (Φ q).2).flip (Φ q).2)))) q.1)
    {x v : E} {T : ℝ} (hT : 0 ≤ T)
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) T, (t, (x, v)) ∈ U) (w : E) :
    G (Φ (T, (x, v))).1
      (fderiv ℝ Φ (T, (x, v)) (0, (0, v))).1
      (fderiv ℝ Φ (T, (x, v)) (0, (0, w))).1 = T ^ 2 * G x v w :=
  flow_gauss_proof hS hG hsym hpos hU hΦ hzero hode hT hseg w

end
end GaussLemma
end

end WeakMTWGlobalSupport

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakMTWGlobalSupport.GaussLemma.gauss_lemma_oai.{u_1} := @OAI.WeakMTWGlobalSupport.GaussLemma.gauss_lemma_oai.{u_1}
