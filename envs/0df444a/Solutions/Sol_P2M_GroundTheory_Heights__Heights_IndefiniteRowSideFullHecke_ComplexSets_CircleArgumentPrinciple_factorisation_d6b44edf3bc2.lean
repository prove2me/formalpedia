-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CircleArgumentPrinciple_factorisation_d6b44edf3bc2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:58.240288+00:00
-- url     : https://prove2.me/submissions/783cad0f-a154-4613-bd9b-baf8ef95e834

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCircleArgumentPrinciple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCircleArgumentPrinciple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Metric Complex Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace CircleArgumentPrinciple
theorem _root_.solution {h : ℂ → ℂ} {O : Set ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hO : IsOpen O) (hball : closedBall c r ⊆ O) (hh : DifferentiableOn ℂ h O)
    (hsph : ∀ s ∈ sphere c r, h s ≠ 0) :
    ∃ (Z : Multiset ℂ) (u : ℂ → ℂ),
      (∀ a ∈ Z, a ∈ ball c r) ∧ DifferentiableOn ℂ u O ∧ (∀ s ∈ closedBall c r, u s ≠ 0) ∧
      (∀ s ∈ O, h s = (Z.map fun a => s - a).prod * u s) := by
  have han : AnalyticOnNhd ℂ h O := hh.analyticOnNhd hO

  have hord : ∀ z ∈ closedBall c r, analyticOrderAt h z ≠ ⊤ := by
    intro z hz htop
    have h0 := (han.mono hball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_closedBall c r).isPreconnected hz (analyticOrderAt_eq_top.1 htop)
    have hs : c + (r : ℂ) ∈ sphere c r := by
      rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hr.le]
    exact hsph _ hs (h0 (sphere_subset_closedBall hs))

  set S0 : Set ℂ := {z | z ∈ closedBall c r ∧ h z = 0} with hS0def
  have hS0fin : S0.Finite := by
    apply IsCompact.finite
    · refine (isCompact_closedBall c r).of_isClosed_subset ?_ (fun z hz => hz.1)
      exact (hh.continuousOn.mono hball).preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
    · rw [isDiscrete_iff_nhdsNE]
      intro z hz
      rcases (han z (hball hz.1)).eventually_eq_zero_or_eventually_ne_zero with h1 | h1
      · exact absurd (analyticOrderAt_eq_top.2 h1) (hord z hz.1)
      · rw [Filter.inf_principal_eq_bot]
        filter_upwards [h1] with w hw hwS
        exact hw hwS.2
  set S : Finset ℂ := hS0fin.toFinset with hSdef
  have hmemS : ∀ a, a ∈ S ↔ a ∈ closedBall c r ∧ h a = 0 := fun a => hS0fin.mem_toFinset
  set m : ℂ → ℕ := fun a => analyticOrderNatAt h a with hmdef
  have hmcast : ∀ a ∈ S, analyticOrderAt h a = (m a : ℕ∞) := fun a ha =>
    (Nat.cast_analyticOrderNatAt (hord a ((hmemS a).1 ha).1)).symm
  have hmpos : ∀ a ∈ S, m a ≠ 0 := by
    intro a ha h0
    have h1 := hmcast a ha
    rw [h0, Nat.cast_zero, analyticOrderAt_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact h1 (han a (hball ((hmemS a).1 ha).1))
    · exact h1 ((hmemS a).1 ha).2
  set P : ℂ → ℂ := fun s => ∏ a ∈ S, (s - a) ^ m a with hPdef
  set Z : Multiset ℂ := ∑ a ∈ S, Multiset.replicate (m a) a with hZdef
  have hPZ : ∀ s, (Z.map fun a => s - a).prod = P s := by
    intro s
    simp only [hZdef, hPdef]
    induction S using Finset.induction_on with
    | empty => simp
    | insert b T hb ih =>
      rw [Finset.sum_insert hb, Finset.prod_insert hb, Multiset.map_add, Multiset.prod_add, ih,
        Multiset.map_replicate, Multiset.prod_replicate]
  have hPdiff : Differentiable ℂ P := by
    simp only [hPdef]
    fun_prop
  have hP0 : ∀ s, P s = 0 ↔ s ∈ S := by
    intro s
    simp only [hPdef, Finset.prod_eq_zero_iff]
    constructor
    · rintro ⟨a, ha, h0⟩
      rw [sub_eq_zero.1 ((pow_eq_zero_iff (hmpos a ha)).1 h0)]
      exact ha
    · intro hs
      exact ⟨s, hs, by rw [sub_self]; exact zero_pow (hmpos s hs)⟩

  have hloc : ∀ a ∈ S, ∃ G : ℂ → ℂ, AnalyticAt ℂ G a ∧ G a ≠ 0 ∧
      ∀ᶠ w in 𝓝[≠] a, P w ≠ 0 ∧ h w / P w = G w := by
    intro a ha
    obtain ⟨g, hg, hga, hev⟩ :=
      (han a (hball ((hmemS a).1 ha).1)).analyticOrderAt_eq_natCast.1 (hmcast a ha)
    set Q : ℂ → ℂ := fun w => ∏ b ∈ S.erase a, (w - b) ^ m b with hQdef
    have hPQ : ∀ w, P w = (w - a) ^ m a * Q w := fun w =>
      (Finset.mul_prod_erase S (fun b => (w - b) ^ m b) ha).symm
    have hQa : Q a ≠ 0 := by
      simp only [hQdef]
      rw [Finset.prod_ne_zero_iff]
      intro b hb
      exact pow_ne_zero _ (sub_ne_zero.2 (Finset.ne_of_mem_erase hb).symm)
    have hQan : AnalyticAt ℂ Q a := by
      simp only [hQdef]
      fun_prop
    refine ⟨fun w => g w / Q w, hg.div hQan hQa, div_ne_zero hga hQa, ?_⟩
    filter_upwards [nhdsWithin_le_nhds hev, nhdsWithin_le_nhds (hQan.continuousAt.eventually_ne hQa),
      self_mem_nhdsWithin] with w hw hQw hwa
    have hpow : (w - a) ^ m a ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hwa)
    refine ⟨by rw [hPQ]; exact mul_ne_zero hpow hQw, ?_⟩
    rw [hw, hPQ, smul_eq_mul, mul_div_mul_left _ _ hpow]
  set u : ℂ → ℂ := fun s => if P s = 0 then limUnder (𝓝[≠] s) (fun w => h w / P w) else h s / P s
    with hudef
  have hu_near : ∀ a ∈ S, ∃ G : ℂ → ℂ, AnalyticAt ℂ G a ∧ G a ≠ 0 ∧ u =ᶠ[𝓝 a] G := by
    intro a ha
    obtain ⟨G, hG, hGa, hev⟩ := hloc a ha
    refine ⟨G, hG, hGa, ?_⟩
    have hlim : limUnder (𝓝[≠] a) (fun w => h w / P w) = G a :=
      Tendsto.limUnder_eq ((hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
        (hev.mono fun w hw => hw.2.symm))
    filter_upwards [eventually_nhdsWithin_iff.1 hev] with w hw
    by_cases hwa : w = a
    · subst hwa
      simp only [hudef, (hP0 w).2 ha, if_true, hlim]
    · obtain ⟨hPw, hq⟩ := hw hwa
      simp only [hudef, hPw, if_false, hq]
  have hu_off : ∀ s, P s ≠ 0 → u =ᶠ[𝓝 s] fun w => h w / P w := by
    intro s hs
    filter_upwards [(hPdiff s).continuousAt.eventually_ne hs] with w hw
    simp only [hudef, hw, if_false]
  refine ⟨Z, u, ?_, ?_, ?_, ?_⟩
  ·
    intro a haZ
    obtain ⟨b, hb, hab⟩ := Multiset.mem_sum.1 haZ
    rw [Multiset.eq_of_mem_replicate hab]
    obtain ⟨hbc, hb0⟩ := (hmemS b).1 hb
    rw [mem_ball]
    refine lt_of_le_of_ne (mem_closedBall.1 hbc) fun hbr => hsph b ?_ hb0
    exact mem_sphere.2 hbr
  ·
    intro s hs
    by_cases hPs : P s = 0
    · obtain ⟨G, hG, -, hEq⟩ := hu_near s ((hP0 s).1 hPs)
      exact (hG.differentiableAt.congr_of_eventuallyEq hEq).differentiableWithinAt
    · exact (((hh.differentiableAt (hO.mem_nhds hs)).div (hPdiff s) hPs).congr_of_eventuallyEq
        (hu_off s hPs)).differentiableWithinAt
  ·
    intro s hs
    by_cases hPs : P s = 0
    · obtain ⟨G, -, hGs, hEq⟩ := hu_near s ((hP0 s).1 hPs)
      rw [hEq.eq_of_nhds]
      exact hGs
    · have hhs : h s ≠ 0 := fun h0 => hPs ((hP0 s).2 ((hmemS s).2 ⟨hs, h0⟩))
      simp only [hudef, hPs, if_false]
      exact div_ne_zero hhs hPs
  ·
    intro s hs
    rw [hPZ]
    by_cases hPs : P s = 0
    · rw [hPs, zero_mul]
      exact ((hmemS s).1 ((hP0 s).1 hPs)).2
    · simp only [hudef, hPs, if_false]
      field_simp
end CircleArgumentPrinciple
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
