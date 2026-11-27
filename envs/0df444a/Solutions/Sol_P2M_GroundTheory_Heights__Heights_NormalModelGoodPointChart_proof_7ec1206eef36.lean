-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_proof_7ec1206eef36
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:05:07.062185+00:00
-- url     : https://prove2.me/submissions/6b5dcaf6-8bef-4e50-804e-d773c9aa603a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelGoodPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticImplicitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GoodPointChartLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelGoodPointChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticImplicitChart_pi_surjective_of_linearIndependent_0f35e360f3ca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_exists_clm_ker_inf_91ac73c5f0ee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_exists_coordChart_fe9e1808ce1e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalModelGoodPointChart_fderiv_eval_apply_c076a1773568


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Topology ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace NormalModelGoodPointChart
theorem _root_.solution : NormalModelGoodPointChart.Statement := by
  classical
  intro n d J u M w hgood
  obtain ⟨hw, c, f, h, g, a, b, k, hc, hfJ, hh, hsat, hg, hli, hk, ha, hb, hrel, himm⟩ := hgood

  let Φ : ((Fin n ⊕ Fin M.m → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] (Fin n ⊕ Fin M.m → ℂ) :=
    { toFun := fun L s => L (Pi.single s 1), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let D : Fin (c + 1) → (Fin n ⊕ Fin M.m → ℂ) →L[ℂ] ℂ :=
    Fin.cons (fderiv ℂ (fun z => eval z g) w) (fun j => fderiv ℂ (fun z => eval z (f j)) w)
  have hDli : LinearIndependent ℂ D := by
    refine LinearIndependent.of_comp Φ ?_
    convert hli using 1
    funext i s
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [D, Φ, NormalModelGoodPointChart.fderiv_eval_apply, Pi.single_apply]
    · simp [D, Φ, NormalModelGoodPointChart.fderiv_eval_apply, Pi.single_apply]
  obtain ⟨A, hA⟩ := NormalModelGoodPointChart.exists_clm_ker_inf
    (LinearMap.pi fun i => (D i : (Fin n ⊕ Fin M.m → ℂ) →ₗ[ℂ] ℂ))
    (IndefiniteRowSideFullHecke.ComplexSets.AnalyticImplicitChart.pi_surjective_of_linearIndependent hDli) d
    (by simp [Module.finrank_fintype_fun_eq_card]; omega)

  let q : Fin (d + 1) ⊕ Fin c → (Fin n ⊕ Fin M.m → ℂ) → ℂ :=
    Sum.elim (Fin.cons (fun z => eval z g) (fun i z => A (z - w) i)) (fun j z => eval z (f j))
  have hq0 : q (Sum.inl 0) = fun z => eval z g := by simp [q]
  have hqs : ∀ i : Fin d, q (Sum.inl i.succ) = fun z => A (z - w) i := fun i => by simp [q]
  have hAd : ∀ (i : Fin d) x, HasFDerivAt (fun z => A (z - w) i)
      ((ContinuousLinearMap.proj i).comp A) x := fun i x => by
    have e : (fun z => A (z - w) i) = fun z => ((ContinuousLinearMap.proj i).comp A) z - A w i := by
      funext z; simp [map_sub]
    rw [e]
    exact ((ContinuousLinearMap.proj i).comp A).hasFDerivAt.sub_const _
  have hqan : ∀ k x, AnalyticAt ℂ (q k) x := by
    intro k x
    rcases k with i | j
    · refine Fin.cases ?_ (fun i => ?_) i
      · rw [hq0]; exact AnalyticOnNhd.eval_mvPolynomial g x trivial
      · rw [hqs]
        have e : (fun z => A (z - w) i) = fun z => ((ContinuousLinearMap.proj i).comp A) z - A w i := by
          funext z; simp [map_sub]
        rw [e]
        exact (((ContinuousLinearMap.proj i).comp A).analyticAt x).sub analyticAt_const
    · exact AnalyticOnNhd.eval_mvPolynomial (f j) x trivial
  set W : Set (Fin n ⊕ Fin M.m → ℂ) := {z | eval z h ≠ 0 ∧ eval z a ≠ 0 ∧ eval z b ≠ 0} with hWdef
  have hWo : IsOpen W :=
    (isOpen_ne_fun (continuous_eval h) continuous_const).inter
      ((isOpen_ne_fun (continuous_eval a) continuous_const).inter
        (isOpen_ne_fun (continuous_eval b) continuous_const))
  obtain ⟨V, O, φ, hVo, hwV, hVW, hOo, hφan, hφV, hφl, hφr, hback, hder⟩ :=
    NormalModelGoodPointChart.exists_coordChart q w W (fun k => hqan k w) (by
      intro v hv
      refine hA v ?_ ?_
      · funext i
        have := hv (Sum.inl i.succ)
        rw [hqs, (hAd i w).fderiv] at this
        simpa using this
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · have := hv (Sum.inl 0)
          rw [hq0] at this
          simpa [D] using this
        · have := hv (Sum.inr j)
          change fderiv ℂ (fun z => eval z (f j)) w v = 0 at this
          simpa [D] using this)
      (by simp; omega) (hWo.mem_nhds ⟨hh, ha, hb⟩)

  have hZf : ∀ z ∈ V, (∀ j, eval z (f j) = 0) → z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal := by
    intro z hz hfz p hp
    obtain ⟨e, he⟩ := hsat p hp
    have hker : Ideal.span (Set.range f) ≤ RingHom.ker (eval z) :=
      Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact RingHom.mem_ker.2 (hfz j))
    have h0 := RingHom.mem_ker.1 (hker he)
    rw [map_mul, map_pow] at h0
    exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ (hVW hz).1)
  have hφZ : ∀ t ∈ O, φ t ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal := fun t ht => hZf _ (hφV t ht) (hφr t ht)

  have hp0 : (fun i => q (Sum.inl i) w) = 0 := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [hq0] using hg
    · simp [hqs]
  obtain ⟨hO0, hφ0⟩ := hback w hwV (fun j => hw _ (hfJ j))
  rw [hp0] at hO0 hφ0
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hOo 0 hO0
  have hpc : Continuous fun z i => q (Sum.inl i) z :=
    continuous_pi fun i => continuous_iff_continuousAt.2 fun x => (hqan _ x).continuousAt
  refine ⟨r, φ, k, hr, fun t ht => (hφan t (hrO ht)).differentiableAt.differentiableWithinAt,
    fun x hx y hy hxy => funext fun i => by rw [← hφl x (hrO hx) i, ← hφl y (hrO hy) i, hxy],
    hφ0, fun t ht => hφZ t (hrO ht), ?_, ?_, ?_⟩
  ·
    intro s hs
    refine ⟨V ∩ (fun z i => q (Sum.inl i) z) ⁻¹' Metric.ball 0 s,
      Filter.inter_mem (hVo.mem_nhds hwV) (hpc.continuousAt.preimage_mem_nhds (by
        rw [hp0]; exact Metric.ball_mem_nhds 0 hs)), ?_⟩
    rintro z ⟨hzZ, hzV, hzs⟩
    exact ⟨_, hzs, (hback z hzV fun j => hzZ _ (hfJ j)).2⟩
  ·
    refine ⟨fun t => eval (φ t) a / eval (φ t) b, ?_, ?_, ?_⟩
    · intro t ht
      have hφt := (hφan t (hrO ht)).differentiableAt
      have h1 : DifferentiableAt ℂ (fun t => eval (φ t) a) t :=
        (AnalyticOnNhd.eval_mvPolynomial a (φ t) trivial).differentiableAt.comp t hφt
      have h2 : DifferentiableAt ℂ (fun t => eval (φ t) b) t :=
        (AnalyticOnNhd.eval_mvPolynomial b (φ t) trivial).differentiableAt.comp t hφt
      have h3 : DifferentiableAt ℂ (fun t => eval (φ t) a * (eval (φ t) b)⁻¹) t :=
        h1.mul (h2.inv (hVW (hφV t (hrO ht))).2.2)
      simpa only [div_eq_mul_inv] using h3.differentiableWithinAt
    · intro t ht
      have hW' := hVW (hφV t (hrO ht))
      exact div_ne_zero hW'.2.1 hW'.2.2
    · intro t ht
      have hW' := hVW (hφV t (hrO ht))
      have hz := hφZ t (hrO ht) _ hrel
      have hgt : eval (φ t) g = t 0 := by simpa [hq0] using hφl t (hrO ht) 0
      have hl : eval (φ t) (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m) (linForm u)) =
          linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t)) := by
        simp [linForm, linEval, IndefiniteRowSideFullHecke.ComplexSets.firstCoords, map_sum]
      simp only [map_sub, map_mul, map_pow, hl, hgt] at hz
      field_simp [hW'.2.2]
      linear_combination hz
  ·
    intro v hv0 hν
    have hDd := hder 0 hO0 v
    rw [hφ0] at hDd
    set x := fderiv ℂ φ 0 v with hx
    let πL : (Fin n ⊕ Fin M.m → ℂ) →L[ℂ] (Fin n → ℂ) :=
      ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ⊕ Fin M.m => ℂ) (Sum.inl i)
    have hπ : HasFDerivAt (fun t => IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t)) (πL.comp (fderiv ℂ φ 0)) 0 :=
      πL.hasFDerivAt.comp 0 (hφan 0 hO0).differentiableAt.hasFDerivAt
    rw [hπ.fderiv] at hν
    have hx0 : x = 0 := by
      refine himm x (fun i => by simpa [πL, hx] using congrFun hν i) ?_ ?_
      · have := hDd.1 0
        rw [hq0, NormalModelGoodPointChart.fderiv_eval_apply] at this
        rw [this, hv0]
      · intro j
        have := hDd.2 j
        rwa [show q (Sum.inr j) = fun z => eval z (f j) from rfl,
          NormalModelGoodPointChart.fderiv_eval_apply] at this
    funext i
    have := hDd.1 i
    rw [hx0, map_zero] at this
    simpa using this.symm
end NormalModelGoodPointChart
end GroundTheory.Heights₂.Heights
