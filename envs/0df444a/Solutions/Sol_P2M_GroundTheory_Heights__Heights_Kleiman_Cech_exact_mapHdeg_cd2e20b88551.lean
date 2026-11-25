-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_exact_mapHdeg_cd2e20b88551
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:01:46.721395+00:00
-- url     : https://prove2.me/submissions/fa36e50b-1c84-4b18-8ab6-ff583cdc2c2b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_eq_zero_73c181096c28
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_eq_mk_1fa86da258c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_surjective_68748e93ef42
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_mapC_injective_1402cce6dfe0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_mapC_mapC_eq_zero_c24cc487b19e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_exists_mapC_eq_61a7961cd0e5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_exists_bdryDeg_of_mem_bdryDeg_22d56b836e02
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_mapHdeg_mk_a6a438d84218
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_mapC_mem_cocyDeg_cf49c96aae0a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.Cech
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R]
  {A B C : Cell U → Type v}
  [∀ I, AddCommGroup (A I)] [∀ I, Module R (A I)]
  [∀ I, AddCommGroup (B I)] [∀ I, Module R (B I)]
  [∀ I, AddCommGroup (C I)] [∀ I, Module R (C I)]
  {ρA : ∀ I J : Cell U, I.1 ⊆ J.1 → A I →ₗ[R] A J}
  {ρB : ∀ I J : Cell U, I.1 ⊆ J.1 → B I →ₗ[R] B J}
  {ρC : ∀ I J : Cell U, I.1 ⊆ J.1 → C I →ₗ[R] C J}
  {dA : ∀ I, Submodule R (A I)} {dB : ∀ I, Submodule R (B I)} {dC : ∀ I, Submodule R (C I)}
  {φ : ∀ I, A I →ₗ[R] B I} {ψ : ∀ I, B I →ₗ[R] C I}
namespace GroundTheory.Heights₂.Heights.Kleiman.Cech
theorem _root_.solution (hφ : ∀ I J h m, φ J (ρA I J h m) = ρB I J h (φ I m))
    (hψ : ∀ I J h m, ψ J (ρB I J h m) = ρC I J h (ψ I m))
    (hφd : ∀ I m, m ∈ dA I → φ I m ∈ dB I) (hψd : ∀ I m, m ∈ dB I → ψ I m ∈ dC I)
    (hinj : ∀ I, Function.Injective (φ I)) (hcomp : ∀ I x, ψ I (φ I x) = 0)
    (hmid : ∀ I, ∀ x ∈ dB I, ψ I x = 0 → ∃ y ∈ dA I, φ I y = x)
    (hsurj : ∀ I, ∀ z ∈ dC I, ∃ x ∈ dB I, ψ I x = z)
    (hρB : ∀ I J h x, x ∈ dB I → ρB I J h x ∈ dB J)
    (hddB : ∀ (i : ℕ) (s : Cochain B i), d B ρB (i + 1) (d B ρB i s) = 0) (i : ℕ) :
    Function.Exact (mapHdeg dA dB φ hφ hφd i) (mapHdeg dB dC ψ hψ hψd i) := by
  intro y
  obtain ⟨z, rfl⟩ := Hdeg_mk_surjective y
  constructor
  · intro h
    rw [mapHdeg_mk hψ hψd z ⟨_, mapC_mem_cocyDeg hψ hψd z.2⟩ rfl, Hdeg_mk_eq_zero] at h
    change mapC ψ i z.1 ∈ bdryDeg C dC ρC i at h
    obtain ⟨x, hxb, hx, hψx, hdx⟩ := exists_bdryDeg_of_mem_bdryDeg hψ hsurj hρB hddB h
    obtain ⟨t, ht, htz⟩ := exists_mapC_eq hmid (sub_mem z.2.2 hx)
      (by rw [map_sub, hψx]; exact sub_self _)
    have htc : t ∈ cocyDeg A dA ρA i := by
      refine ⟨LinearMap.mem_ker.2 (mapC_injective hinj (i + 1) ?_), ht⟩
      rw [mapC_d φ hφ, htz, map_sub, LinearMap.mem_ker.1 z.2.1, hdx, sub_zero, map_zero]
    refine ⟨Hdeg.mk ⟨t, htc⟩, ?_⟩
    rw [mapHdeg_mk hφ hφd ⟨t, htc⟩ ⟨_, mapC_mem_cocyDeg hφ hφd htc⟩ rfl, Hdeg_mk_eq_mk]
    change mapC φ i t - z.1 ∈ _
    rw [htz, sub_sub_cancel_left]
    exact Submodule.neg_mem _ hxb
  · rintro ⟨y, hy⟩
    obtain ⟨t, rfl⟩ := Hdeg_mk_surjective y
    rw [← hy, mapHdeg_mk hφ hφd t ⟨_, mapC_mem_cocyDeg hφ hφd t.2⟩ rfl,
      mapHdeg_mk hψ hψd _ ⟨_, mapC_mem_cocyDeg hψ hψd (mapC_mem_cocyDeg hφ hφd t.2)⟩ rfl,
      Hdeg_mk_eq_zero]
    change mapC ψ i (mapC φ i t.1) ∈ _
    rw [mapC_mapC_eq_zero hcomp]
    exact Submodule.zero_mem _
end GroundTheory.Heights₂.Heights.Kleiman.Cech
