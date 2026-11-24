-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_exists_bdryDeg_of_mem_bdryDeg_22d56b836e02
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:29.384531+00:00
-- url     : https://prove2.me/submissions/27bec364-32b0-44cb-9ced-3e931783f266

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_exists_mapC_eq_of_mem_e11fe874719c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_d_mem_Cdeg_40a32403d833

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
theorem _root_.solution (hψ : ∀ I J h m, ψ J (ρB I J h m) = ρC I J h (ψ I m))
    (hsurj : ∀ I, ∀ z ∈ dC I, ∃ x ∈ dB I, ψ I x = z)
    (hρB : ∀ I J h x, x ∈ dB I → ρB I J h x ∈ dB J)
    (hddB : ∀ (i : ℕ) (s : Cochain B i), d B ρB (i + 1) (d B ρB i s) = 0) {i : ℕ}
    {s : Cochain C i} (hs : s ∈ bdryDeg C dC ρC i) :
    ∃ x, x ∈ bdryDeg B dB ρB i ∧ x ∈ Cdeg B dB i ∧ mapC ψ i x = s ∧ d B ρB i x = 0 := by
  cases i with
  | zero =>
    have h0 : s ∈ (⊥ : Submodule R (Cochain C 0)) := hs
    rw [Submodule.mem_bot] at h0
    exact ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, by rw [map_zero, h0], map_zero _⟩
  | succ k =>
    obtain ⟨y'', hy'', rfl⟩ := hs
    obtain ⟨y, hy, rfl⟩ := exists_mapC_eq_of_mem hsurj hy''
    exact ⟨d B ρB k y, ⟨y, hy, rfl⟩, d_mem_Cdeg hρB hy, mapC_d ψ hψ k y, hddB k y⟩
end GroundTheory.Heights₂.Heights.Kleiman.Cech
