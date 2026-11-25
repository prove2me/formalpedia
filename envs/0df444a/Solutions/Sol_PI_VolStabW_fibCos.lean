-- Prove2me | solution 1 for PI.VolStabW.fibCos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:32:47.012833+00:00
-- url     : https://prove2.me/submissions/f4d81974-1c84-41cf-8366-20c0fa3b4fa1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_HenselCountHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHF
import Theorems.Thm_PI_VolStabW_fib_of_ratio
import Theorems.Thm_PI_VolStabW_cos_ratio

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
open MeasureTheory Topology Filter Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
namespace PI.VolStabW
theorem _root_.solution (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (f : V → Y) (ι : X → Y) (hι : Function.Injective ι) (G : V → X) (hGc : Continuous G)
    (hfG : ∀ x, f x = ι (G x)) (U : Set V) (B : Set X) (fib : X → Measure V)
    (hfib : IsFibreFamily μ f ι U ν B fib) (T : X) (hB : B ∈ 𝓝 T) (Nb : Set X) (hNb : Nb ∈ 𝓝 T)
    (hNbU : ∀ x, G x ∈ Nb → x ∈ U)
    (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set V))
    (hΛc : ∀ n, IsCompact (Λ n : Set V)) (hΛa : Antitone Λ) (hHo : ∀ n, IsOpen (H n : Set X))
    (hHc : ∀ n, IsCompact (H n : Set X)) (hHb : ∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N')
    (D : V →+ X) (hD : ∀ n, (Λ n).map D = H n) (y : V)
    (hG : ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1))
    (hyT : G y - T ∈ H 0) :
    ∫ x, {x | x - y ∈ Λ 0}.indicator (1 : V → ℂ) x ∂(fib T) =
      (((μ (Λ 0 : Set V)) / ν (H 0)).toReal : ℂ) := by
  have hQe : {x | x - y ∈ Λ 0} = (fun x => x + -y) ⁻¹' (Λ 0 : Set V) := by
    ext x; simp [sub_eq_add_neg]
  have hQo : IsOpen {x | x - y ∈ Λ 0} := (hΛo 0).preimage (continuous_id.sub continuous_const)
  have hQcl : IsClosed {x | x - y ∈ Λ 0} :=
    (AddSubgroup.isClosed_of_isOpen _ (hΛo 0)).preimage (continuous_id.sub continuous_const)
  have hQc : IsCompact {x | x - y ∈ Λ 0} := by
    have : {x | x - y ∈ Λ 0} = (fun w => w + y) '' (Λ 0 : Set V) := by
      ext z
      simp only [mem_setOf_eq, mem_image, SetLike.mem_coe]
      constructor
      · intro hz
        exact ⟨z - y, hz, by abel⟩
      · rintro ⟨w, hw, rfl⟩
        simpa using hw
    rw [this]
    exact (hΛc 0).image (continuous_id.add continuous_const)
  have hν0 : 0 < ν.real (H 0) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos ((hHo 0).measure_pos ν ⟨0, (H 0).zero_mem⟩).ne'
      (hHc 0).measure_lt_top.ne
  have hratio : ∀ n, μ.real ({x | x - y ∈ Λ 0} ∩ G ⁻¹' {z | z - T ∈ H n}) =
      μ.real (Λ 0 : Set V) / ν.real (H 0) * ν.real (H n) := by
    intro n
    have e := cos_ratio μ ν Λ H hΛo hΛa hHo hHc D hD G y hG T hyT n
    have e' := congrArg ENNReal.toReal e
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at e'
    simp only [← measureReal_def] at e'
    field_simp
    linarith
  rw [fib_of_ratio μ ν f ι hι G hGc hfG U B fib hfib T hB Nb hNb hNbU _ hQo hQcl hQc H hHo hHc
    hHb _ hratio, ENNReal.toReal_div, measureReal_def, measureReal_def]
end PI.VolStabW
