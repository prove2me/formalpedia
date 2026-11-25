-- Prove2me | solution 1 for PI.VolStabW.densCos_of_filt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:56.098395+00:00
-- url     : https://prove2.me/submissions/7664d7fa-3d6a-4ac5-85ee-c2b391f3adec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVCos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_HenselCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_CosDens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVGlue
import Theorems.Thm_PI_VolStabW_HasDens_sub
import Theorems.Thm_PI_VolStabW_isCompact_cos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Topology Set
namespace PI.VolStabW
theorem _root_.solution (hP1 : HenselCount) (hP2 : CosDens) {V X Y : Type} [AddCommGroup V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V]
    [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure]
    [ν.IsAddHaarMeasure] (f : V → Y) (ι : X → Y) (hι : Function.Injective ι) (G : V → X)
    (hG : Continuous G) (hfG : ∀ v, f v = ι (G v)) (y : V) (Λ : ℕ → AddSubgroup V)
    (H : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set V)) (hΛc : ∀ n, IsCompact (Λ n : Set V))
    (hΛa : Antitone Λ) (hHo : ∀ n, IsOpen (H n : Set X)) (hHc : ∀ n, IsCompact (H n : Set X))
    (hHb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N) (D : V →+ X) (hD : ∀ n, (Λ n).map D = H n)
    (hyp : ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1)) :
    ∃ g : X → ℝ, Continuous g ∧ ∀ S : Set X, IsCompact S →
      ∫ v in f ⁻¹' (ι '' S), {z | z - y ∈ Λ 0}.indicator (fun _ => (1 : ℝ)) v ∂μ =
        ∫ b in S, g b ∂ν := by
  have hHa : Antitone H := fun m n hmn => by
    rw [← hD, ← hD]
    exact AddSubgroup.map_mono (hΛa hmn)
  set Q : Set V := {z | z - y ∈ Λ 0} with hQ
  have hQm : MeasurableSet Q := ((hΛo 0).preimage (continuous_id.sub continuous_const)).measurableSet
  have hQf : μ Q ≠ ⊤ := (isCompact_cos (Λ 0) (hΛc 0) y).measure_lt_top.ne
  set C : Set X := {z | z - G y ∈ H 0} with hC
  have hCo : IsOpen C := (hHo 0).preimage (continuous_id.sub continuous_const)
  have hCcl : IsClosed C :=
    (AddSubgroup.isClosed_of_isOpen _ (hHo 0)).preimage (continuous_id.sub continuous_const)
  have hGm : Measurable G := hG.measurable
  set m : Measure X := (μ.restrict Q).map G with hm
  have : IsFiniteMeasure (μ.restrict Q) := ⟨by rw [Measure.restrict_apply_univ]; exact hQf.lt_top⟩
  have : IsFiniteMeasure m := by rw [hm]; infer_instance
  have hcos_m : ∀ (h : X) (n : ℕ), m {z | z - h ∈ H n} =
      μ {Z | Z ∈ Λ 0 ∧ G (y + Z) - h ∈ H n} := by
    intro h n
    have hmeas : MeasurableSet {z : X | z - h ∈ H n} :=
      ((hHo n).preimage (continuous_id.sub continuous_const)).measurableSet
    rw [hm, Measure.map_apply hGm hmeas, Measure.restrict_apply (hGm hmeas)]
    have : G ⁻¹' {z | z - h ∈ H n} ∩ Q =
        (fun X => -y + X) ⁻¹' {Z | Z ∈ Λ 0 ∧ G (y + Z) - h ∈ H n} := by
      ext X
      simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, hQ, neg_add_eq_sub]
      rw [add_sub_cancel]
      exact and_comm
    rw [this, measure_preimage_add]
  have hcos_ν : ∀ (h : X) (n : ℕ), ν {z | z - h ∈ H n} = ν (H n) := by
    intro h n
    have : {z | z - h ∈ H n} = (fun z => -h + z) ⁻¹' (H n : Set X) := by
      ext z
      simp [neg_add_eq_sub]
    rw [this, measure_preimage_add]
  have hH0 : ν (H 0) ≠ 0 := ((hHo 0).measure_pos ν ⟨0, (H 0).zero_mem⟩).ne'
  have hH0t : ν (H 0) ≠ ⊤ := (hHc 0).measure_lt_top.ne
  set κ : ENNReal := μ (Λ 0) * (ν (H 0))⁻¹ with hκ
  have hcos : ∀ n h, h - G y ∈ H 0 → m {z | z - h ∈ H n} = κ * ν {z | z - h ∈ H n} := by
    intro n h hh
    have e := hP1 V X μ ν inferInstance inferInstance Λ H hΛo hΛc hΛa hHo hHc D hD G y hyp n h hh
    rw [hcos_m, hcos_ν]
    calc μ {Z | Z ∈ Λ 0 ∧ G (y + Z) - h ∈ H n}
        = μ {Z | Z ∈ Λ 0 ∧ G (y + Z) - h ∈ H n} * (ν (H 0) * (ν (H 0))⁻¹) := by
          rw [ENNReal.mul_inv_cancel hH0 hH0t, mul_one]
      _ = μ {Z | Z ∈ Λ 0 ∧ G (y + Z) - h ∈ H n} * ν (H 0) * (ν (H 0))⁻¹ := (mul_assoc _ _ _).symm
      _ = μ (Λ 0) * ν (H n) * (ν (H 0))⁻¹ := by rw [e]
      _ = κ * ν (H n) := by rw [hκ]; ring
  have hCc : m Cᶜ = 0 := by
    rw [hm, Measure.map_apply hGm hCo.measurableSet.compl, Measure.restrict_apply (hGm hCo.measurableSet.compl)]
    have : G ⁻¹' Cᶜ ∩ Q = ∅ := by
      ext X
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, hC, hQ, mem_setOf_eq,
        mem_empty_iff_false, iff_false, not_and]
      intro hn hX
      have e1 := hyp 0 0 (Λ 0).zero_mem (X - y) hX
      have e2 : D (X - y) ∈ H 0 := by rw [← hD 0]; exact ⟨X - y, hX, rfl⟩
      have e3 := (H 0).add_mem (hHa (Nat.zero_le 1) e1) e2
      simp only [add_zero, add_sub_cancel] at e3
      exact hn (by simpa [sub_add_cancel] using e3)
    rw [this, measure_empty]
  have key := hP2 X ν m inferInstance H hHo hHc hHa hHb (G y) κ hCc hcos
  have hgc : Continuous (C.indicator fun _ => (1 : ℝ)) := by
    refine IsLocallyConstant.continuous ?_
    rw [IsLocallyConstant.iff_exists_open]
    intro b
    by_cases hb : b ∈ C
    · exact ⟨C, hCo, hb, fun b' hb' => by rw [indicator_of_mem hb', indicator_of_mem hb]⟩
    · exact ⟨Cᶜ, hCcl.isOpen_compl, hb, fun b' hb' => by
        rw [indicator_of_notMem hb', indicator_of_notMem hb]⟩
  refine ⟨fun b => κ.toReal * C.indicator (fun _ => (1 : ℝ)) b, continuous_const.mul hgc,
    fun S hS => ?_⟩
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hP : f ⁻¹' (ι '' S) = G ⁻¹' S := by
    ext X
    simp only [mem_preimage, mem_image, hfG]
    exact ⟨fun ⟨s, hs, e⟩ => hι e ▸ hs, fun h => ⟨G X, h, rfl⟩⟩
  rw [hP, integral_indicator_const _ hQm, integral_const_mul, integral_indicator_const _ hCo.measurableSet,
    Measure.real, Measure.real, Measure.restrict_apply hQm, Measure.restrict_apply hCo.measurableSet,
    smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.toReal_mul]
  congr 1
  have e := key S hS
  rw [hm, Measure.map_apply hGm hSm, Measure.restrict_apply (hGm hSm)] at e
  rw [inter_comm, e, inter_comm]
end PI.VolStabW
