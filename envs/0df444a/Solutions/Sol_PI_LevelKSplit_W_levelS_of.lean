-- Prove2me | solution 1 for PI.LevelKSplit.W.levelS_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:50:51.615809+00:00
-- url     : https://prove2.me/submissions/cd04be27-54fc-4593-91df-ae340f0fbbb2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LevelKSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
variable {F E σ M J}
namespace PI.LevelKSplit.W
theorem _root_.solution (hinv : ∀ x, σ (σ x) = x) (hEx : ExistS F E σ M J) (hMe : MeasKf F E σ M J) (hSp : SplitK F E σ M J) :
    LevelS F E σ M J := by
  intro hJ r P T hP ΛX ΛW ΛY hA μN hμN μH hμH
  refine ⟨hEx r P T hP μN hμN μH hμH, ?_⟩
  rintro μS ⟨-, hprod⟩
  have hKm : MeasurableSet (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) := hMe _
  have key := hprod ((Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)).indicator 1)
    (measurable_one.indicator hKm)
  have hS : {s : Ssub (Af F) σ J P | (s : HA (Af F) σ J) ∈ KS σ J P (ΛX ∪ ΛW ∪ ΛY)} =
      Subtype.val ⁻¹' (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) := by
    ext s
    show (s : HA (Af F) σ J) ∈ Ssub (Af F) σ J P ⊓ Kf σ J (ΛX ∪ ΛW ∪ ΛY) ↔
      (s : HA (Af F) σ J) ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY)
    rw [Subgroup.mem_inf]
    exact ⟨And.right, fun h => ⟨s.2, h⟩⟩
  have hN : {m : Nsub (Af F) σ J P | (m : HA (Af F) σ J) ∈ NO σ J P (ΛX ∪ ΛW ∪ ΛY)} =
      Subtype.val ⁻¹' (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) := by
    ext s
    show (s : HA (Af F) σ J) ∈ Nsub (Af F) σ J P ⊓ Kf σ J (ΛX ∪ ΛW ∪ ΛY) ↔
      (s : HA (Af F) σ J) ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY)
    rw [Subgroup.mem_inf]
    exact ⟨And.right, fun h => ⟨s.2, h⟩⟩
  have hH : {m : Hsub (Af F) σ J P | (m : HA (Af F) σ J) ∈ KH σ J P (ΛX ∪ ΛW ∪ ΛY)} =
      Subtype.val ⁻¹' (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) := by
    ext s
    show (s : HA (Af F) σ J) ∈ Hsub (Af F) σ J P ⊓ Kf σ J (ΛX ∪ ΛW ∪ ΛY) ↔
      (s : HA (Af F) σ J) ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY)
    rw [Subgroup.mem_inf]
    exact ⟨And.right, fun h => ⟨s.2, h⟩⟩
  rw [hS, hN, hH]
  have hL : ∫⁻ k, (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)).indicator 1
      (k : HA (Af F) σ J) ∂μS = μS (Subtype.val ⁻¹' (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J))) := by
    rw [← lintegral_indicator_one (measurable_subtype_coe hKm)]
    congr 1
  have inner : ∀ m : Nsub (Af F) σ J P,
      ∫⁻ h, (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)).indicator 1
        ((m : HA (Af F) σ J) * (h : HA (Af F) σ J)) ∂μH =
      (Subtype.val ⁻¹' (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J))).indicator
        (fun _ => μH (Subtype.val ⁻¹' (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)))) m := by
    intro m
    by_cases hm : (m : HA (Af F) σ J) ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY)
    · rw [Set.indicator_of_mem (show m ∈ Subtype.val ⁻¹'
          (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) from hm),
        ← lintegral_indicator_one (measurable_subtype_coe hKm)]
      congr 1
      funext h
      by_cases hh : (h : HA (Af F) σ J) ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY)
      · simp only [Set.indicator_of_mem (show (m : HA (Af F) σ J) * (h : HA (Af F) σ J) ∈
            (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) from (Kf σ J _).mul_mem hm hh),
          Set.indicator_of_mem (show h ∈ Subtype.val ⁻¹'
            (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) from hh), Pi.one_apply]
      · rw [Set.indicator_of_notMem (show (m : HA (Af F) σ J) * (h : HA (Af F) σ J) ∉
            (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) from
              fun hmh => hh (hSp hJ hinv r P T hP ΛX ΛW ΛY hA m h m.2 h.2 hmh)),
          Set.indicator_of_notMem (show h ∉ Subtype.val ⁻¹'
            (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) from hh)]
    · rw [Set.indicator_of_notMem (show m ∉ Subtype.val ⁻¹'
          (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)) from hm)]
      have hz : ∀ h : Hsub (Af F) σ J P, (Kf σ J (ΛX ∪ ΛW ∪ ΛY) : Set (HA (Af F) σ J)).indicator 1
          ((m : HA (Af F) σ J) * (h : HA (Af F) σ J)) = (0 : ENNReal) := by
        intro h
        refine Set.indicator_of_notMem (fun hmh => hm ?_) _
        have hh := hSp hJ hinv r P T hP ΛX ΛW ΛY hA m h m.2 h.2 hmh
        have h2 := (Kf σ J (ΛX ∪ ΛW ∪ ΛY)).mul_mem hmh ((Kf σ J (ΛX ∪ ΛW ∪ ΛY)).inv_mem hh)
        rwa [mul_inv_cancel_right] at h2
      simp only [hz, lintegral_zero]
  rw [hL, lintegral_congr inner, lintegral_indicator_const (measurable_subtype_coe hKm)] at key
  rw [key, mul_comm]
end PI.LevelKSplit.W
