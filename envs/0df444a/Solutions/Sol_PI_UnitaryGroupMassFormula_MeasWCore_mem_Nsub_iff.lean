-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.MeasWCore.mem_Nsub_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:58:53.348226+00:00
-- url     : https://prove2.me/submissions/b92a4632-a7e9-46fd-afc7-735dd4b7afb2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_SplTApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_MemSpanRIffSplit
import Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_mapV_ratV
import Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_lin_haMap
import Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_mapV_mem_spanR
import Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_hR_mapV
import Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_hR_zero_right
import Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_exists_split
import Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_Memb_mem_spanR_iff_split
import Theorems.Thm_PI_UnitaryGroupMassFormula_MeasWCore_splT_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.MeasWCore
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField
open scoped TensorProduct
open Memb
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)
namespace PI.UnitaryGroupMassFormula.MeasWCore
theorem _root_.solution (hbij : Function.Bijective (splT (F := F) (E := E))) {r : ℕ} (P : Frame E n r)
    (g : HA (AF F) σ J) :
    g ∈ Nsub (AF F) σ J P ↔ haMap σ J (fstA F) g ∈ Nsub (Ainf F) σ J P ∧
      haMap σ J (sndA F) g ∈ Nsub (Af F) σ J P := by
  have hdiff : ∀ {R' : Type} [CommRing R'] [Algebra F R'] (φ : AF F →ₐ[F] R') (v : Fin n → AF F ⊗[F] E),
      mapV (E := E) φ (lin (AF F) σ J g v - v) =
        lin R' σ J (haMap σ J φ g) (mapV (E := E) φ v) - mapV (E := E) φ v := by
    intro R' _ _ φ v
    rw [map_sub, lin_haMap]
  have hperp : ∀ {R' : Type} [CommRing R'] [Algebra F R'] (φ : AF F →ₐ[F] R') (v : Fin n → AF F ⊗[F] E),
      InXperp (AF F) σ J P v → InXperp R' σ J P (mapV (E := E) φ v) := by
    intro R' _ _ φ v hv a
    rw [← mapV_ratV φ, hR_mapV, hv a, map_zero]
  change (UniC (AF F) σ J P.e g ∧ ∀ v, InXperp (AF F) σ J P v →
      lin (AF F) σ J g v - v ∈ spanR (F := F) (AF F) P.e Set.univ) ↔
    (UniC (Ainf F) σ J P.e (haMap σ J (fstA F) g) ∧ ∀ v, InXperp (Ainf F) σ J P v →
      lin (Ainf F) σ J (haMap σ J (fstA F) g) v - v ∈ spanR (F := F) (Ainf F) P.e Set.univ) ∧
    (UniC (Af F) σ J P.e (haMap σ J (sndA F) g) ∧ ∀ v, InXperp (Af F) σ J P v →
      lin (Af F) σ J (haMap σ J (sndA F) g) v - v ∈ spanR (F := F) (Af F) P.e Set.univ)
  have huni : UniC (AF F) σ J P.e g ↔ UniC (Ainf F) σ J P.e (haMap σ J (fstA F) g) ∧
      UniC (Af F) σ J P.e (haMap σ J (sndA F) g) := by
    unfold UniC
    constructor
    · intro h
      refine ⟨fun b => ?_, fun b => ?_⟩
      · have := mapV_mem_spanR (E := E) (fstA F) P.e _ _ (h b)
        rwa [hdiff, mapV_ratV] at this
      · have := mapV_mem_spanR (E := E) (sndA F) P.e _ _ (h b)
        rwa [hdiff, mapV_ratV] at this
    · rintro ⟨h1, h2⟩ b
      rw [mem_spanR_iff_split hbij, hdiff, hdiff, mapV_ratV, mapV_ratV]
      exact ⟨h1 b, h2 b⟩
  rw [huni]
  constructor
  · rintro ⟨⟨hu1, hu2⟩, hX⟩
    refine ⟨⟨hu1, fun v₁ hv₁ => ?_⟩, ⟨hu2, fun v₂ hv₂ => ?_⟩⟩
    · obtain ⟨v, hv1, hv2⟩ := exists_split hbij.2 v₁ 0
      have hv : InXperp (AF F) σ J P v := by
        intro a
        apply hbij.1
        rw [map_zero, splT_apply, ← hR_mapV, ← hR_mapV, mapV_ratV, mapV_ratV, hv1, hv2,
          hR_zero_right, hv₁ a]
        rfl
      have := mapV_mem_spanR (E := E) (fstA F) P.e _ _ (hX v hv)
      rwa [hdiff, hv1] at this
    · obtain ⟨v, hv1, hv2⟩ := exists_split hbij.2 0 v₂
      have hv : InXperp (AF F) σ J P v := by
        intro a
        apply hbij.1
        rw [map_zero, splT_apply, ← hR_mapV, ← hR_mapV, mapV_ratV, mapV_ratV, hv1, hv2,
          hR_zero_right, hv₂ a]
        rfl
      have := mapV_mem_spanR (E := E) (sndA F) P.e _ _ (hX v hv)
      rwa [hdiff, hv2] at this
  · rintro ⟨⟨hu1, hX1⟩, ⟨hu2, hX2⟩⟩
    refine ⟨⟨hu1, hu2⟩, fun v hv => ?_⟩
    rw [mem_spanR_iff_split hbij, hdiff, hdiff]
    exact ⟨hX1 _ (hperp _ v hv), hX2 _ (hperp _ v hv)⟩
end PI.UnitaryGroupMassFormula.MeasWCore
