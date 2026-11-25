-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_longExact_09831fd84e20
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:08.98319+00:00
-- url     : https://prove2.me/submissions/eb228711-4ab1-4f10-a7fe-d10172258c5b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_eq_zero_73c181096c28
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_eq_mk_1fa86da258c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_surjective_68748e93ef42
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_zero_7e32b064706a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_add_c14589756398
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_smul_5019c3cbefe7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_mapC_mem_Cdeg_468fb0d14ac9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_mapC_injective_1402cce6dfe0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_mapC_mapC_eq_zero_c24cc487b19e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_exists_mapC_eq_61a7961cd0e5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_exists_mapC_eq_of_mem_e11fe874719c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_d_mem_Cdeg_40a32403d833
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_exists_bdryDeg_of_mem_bdryDeg_22d56b836e02
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_mapHdeg_mk_a6a438d84218
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_mapC_mem_cocyDeg_cf49c96aae0a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_exact_mapHdeg_cd2e20b88551

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
    (hddB : ∀ (i : ℕ) (s : Cochain B i), d B ρB (i + 1) (d B ρB i s) = 0) :
    Function.Injective (mapHdeg dA dB φ hφ hφd 0) ∧
      ∀ i : ℕ, Function.Exact (mapHdeg dA dB φ hφ hφd i) (mapHdeg dB dC ψ hψ hψd i) ∧
        ∃ δ : Hdeg C dC ρC i →ₗ[R] Hdeg A dA ρA (i + 1),
          Function.Exact (mapHdeg dB dC ψ hψ hψd i) δ ∧ Function.Exact δ (mapHdeg dA dB φ hφ hφd (i + 1)) := by
  refine ⟨?_, fun i => ⟨exact_mapHdeg hφ hψ hφd hψd hinj hcomp hmid hsurj hρB hddB i, ?_⟩⟩
  · refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
    obtain ⟨z, rfl⟩ := Hdeg_mk_surjective y
    rw [mapHdeg_mk hφ hφd z ⟨_, mapC_mem_cocyDeg hφ hφd z.2⟩ rfl, Hdeg_mk_eq_zero] at hy
    have h0 : mapC φ 0 z.1 ∈ (⊥ : Submodule R (Cochain B 0)) := hy
    rw [Submodule.mem_bot, ← map_zero (mapC φ 0)] at h0
    have hz : z = 0 := Subtype.ext (mapC_injective hinj 0 h0)
    rw [hz, Hdeg_mk_zero]

  choose lift hlift_mem hlift using fun z : cocyDeg C dC ρC i => exists_mapC_eq_of_mem hsurj z.2.2
  choose w hw_mem hw using fun z : cocyDeg C dC ρC i =>
    exists_mapC_eq hmid (d_mem_Cdeg hρB (hlift_mem z))
      (by rw [mapC_d ψ hψ, hlift]; exact LinearMap.mem_ker.1 z.2.1)
  have hw_cocy : ∀ z, w z ∈ cocyDeg A dA ρA (i + 1) := fun z =>
    ⟨LinearMap.mem_ker.2 (mapC_injective hinj (i + 1 + 1) (by
      rw [mapC_d φ hφ, hw, hddB, map_zero])), hw_mem z⟩

  have key : ∀ (z : cocyDeg C dC ρC i) (x : Cochain B i), x ∈ Cdeg B dB i → mapC ψ i x = z.1 →
      ∀ y : cocyDeg A dA ρA (i + 1), mapC φ (i + 1) y.1 = d B ρB i x →
        Hdeg.mk ⟨w z, hw_cocy z⟩ = Hdeg.mk y := by
    intro z x hx hψx y hy
    rw [Hdeg_mk_eq_mk]
    obtain ⟨u, hu, hφu⟩ := exists_mapC_eq hmid (sub_mem (hlift_mem z) hx)
      (by rw [map_sub, hlift, hψx]; exact sub_self _)
    refine ⟨u, hu, mapC_injective hinj (i + 1) ?_⟩
    change mapC φ (i + 1) (d A ρA i u) = mapC φ (i + 1) (w z - y.1)
    rw [mapC_d φ hφ, hφu, map_sub, map_sub, hw z, hy]
  let δ₀ : cocyDeg C dC ρC i →ₗ[R] Hdeg A dA ρA (i + 1) :=
    { toFun := fun z => Hdeg.mk ⟨w z, hw_cocy z⟩
      map_add' := fun a b => by
        rw [← Hdeg_mk_add]
        exact key (a + b) (lift a + lift b) (Submodule.add_mem _ (hlift_mem a) (hlift_mem b))
          (by rw [map_add, hlift, hlift]; rfl) (⟨w a, hw_cocy a⟩ + ⟨w b, hw_cocy b⟩)
          (by change mapC φ (i + 1) (w a + w b) = _; rw [map_add, map_add, hw, hw])
      map_smul' := fun r a => by
        rw [RingHom.id_apply, ← Hdeg_mk_smul]
        exact key (r • a) (r • lift a) (Submodule.smul_mem _ r (hlift_mem a))
          (by rw [map_smul, hlift]; rfl) (r • ⟨w a, hw_cocy a⟩)
          (by change mapC φ (i + 1) (r • w a) = _; rw [map_smul, map_smul, hw]) }
  have hδ₀ : ∀ z, δ₀ z = Hdeg.mk ⟨w z, hw_cocy z⟩ := fun _ => rfl
  have hker : (bdryDeg C dC ρC i).comap (cocyDeg C dC ρC i).subtype ≤ LinearMap.ker δ₀ := by
    intro z hz
    rw [Submodule.mem_comap] at hz
    obtain ⟨x, -, hx, hψx, hdx⟩ := exists_bdryDeg_of_mem_bdryDeg hψ hsurj hρB hddB hz
    rw [LinearMap.mem_ker, hδ₀, key z x hx hψx 0 (by rw [hdx]; exact map_zero _)]
    exact Hdeg_mk_zero
  let δ : Hdeg C dC ρC i →ₗ[R] Hdeg A dA ρA (i + 1) := Submodule.liftQ _ δ₀ hker
  have hδ : ∀ z, δ (Hdeg.mk z) = δ₀ z := fun _ => rfl
  refine ⟨δ, ?_, ?_⟩
  ·
    intro y
    obtain ⟨z, rfl⟩ := Hdeg_mk_surjective y
    constructor
    · intro h
      rw [hδ, hδ₀, Hdeg_mk_eq_zero] at h
      obtain ⟨u, hu, hdu⟩ := h
      change d A ρA i u = w z at hdu
      have hxc : lift z - mapC φ i u ∈ cocyDeg B dB ρB i := by
        refine ⟨LinearMap.mem_ker.2 ?_, Submodule.sub_mem _ (hlift_mem z) (mapC_mem_Cdeg hφd hu)⟩
        rw [map_sub, ← mapC_d φ hφ, hdu, hw z, sub_self]
      refine ⟨Hdeg.mk ⟨_, hxc⟩, mapHdeg_mk hψ hψd ⟨_, hxc⟩ z ?_⟩
      change mapC ψ i (lift z - mapC φ i u) = z.1
      rw [map_sub, hlift, mapC_mapC_eq_zero hcomp, sub_zero]
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := Hdeg_mk_surjective y
      rw [← hy, mapHdeg_mk hψ hψd x ⟨_, mapC_mem_cocyDeg hψ hψd x.2⟩ rfl, hδ, hδ₀,
        key _ x.1 x.2.2 rfl 0 (by rw [LinearMap.mem_ker.1 x.2.1]; exact map_zero _)]
      exact Hdeg_mk_zero
  ·
    intro x
    obtain ⟨y, rfl⟩ := Hdeg_mk_surjective x
    constructor
    · intro h
      rw [mapHdeg_mk hφ hφd y ⟨_, mapC_mem_cocyDeg hφ hφd y.2⟩ rfl, Hdeg_mk_eq_zero] at h
      change mapC φ (i + 1) y.1 ∈ bdryDeg B dB ρB (i + 1) at h
      obtain ⟨x, hx, hxy⟩ := h
      have hz : mapC ψ i x ∈ cocyDeg C dC ρC i :=
        ⟨LinearMap.mem_ker.2 (by rw [← mapC_d ψ hψ, hxy, mapC_mapC_eq_zero hcomp]),
          mapC_mem_Cdeg hψd hx⟩
      refine ⟨Hdeg.mk ⟨_, hz⟩, ?_⟩
      rw [hδ, hδ₀]
      exact key _ x hx rfl y hxy.symm
    · rintro ⟨x, hx⟩
      obtain ⟨z, rfl⟩ := Hdeg_mk_surjective x
      rw [← hx, hδ, hδ₀,
        mapHdeg_mk hφ hφd ⟨w z, hw_cocy z⟩ ⟨_, mapC_mem_cocyDeg hφ hφd (hw_cocy z)⟩ rfl,
        Hdeg_mk_eq_zero]
      change mapC φ (i + 1) (w z) ∈ bdryDeg B dB ρB (i + 1)
      rw [hw z]
      exact ⟨lift z, hlift_mem z, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman.Cech
