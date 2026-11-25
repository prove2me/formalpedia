-- Prove2me | solution 1 for PI.DvRows.localGamma_of_gramCS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:28:16.80091+00:00
-- url     : https://prove2.me/submissions/1c98af86-1214-4e64-b3bb-ba6e2eba3fc3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Theorems.Thm_PI_DvRows_lattice_finitely_generated
import Theorems.Thm_PI_DvRows_lidx_zero_of_loc
import Theorems.Thm_P2M_PI_DvRows_lidx_add_of_span_eq__d114b9139d51
import Theorems.Thm_P2M_PI_DvRows_vAdd_mul__c62e31a6c4e3
import Theorems.Thm_PI_DvRows_conj_unique
import Theorems.Thm_PI_DvRows_lidx_span_act
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
open Formalism.HermitianLatticesTheory
namespace PI.DvRows
theorem _root_.solution (hG : GramCS) : LocalGamma := by
  intro K _ _ _ _ _ A e n h hyp U hU d y hy hyL hspan w k hk w' hw'
  obtain ⟨w'', hw'', d'', y'', hy'', hloc, hkk⟩ := hk
  have hww : w'' = w' := conj_unique hw'' hw'
  subst hww
  subst hkk
  set L := lamSub A e h U with hL
  have hLfg : L.FG := lattice_finitely_generated K A e n h hyp U hU
  have hlw := hloc w (Set.mem_insert _ _)
  have hlw' := hloc w'' (Set.mem_insert_of_mem _ rfl)
  have hs0 : ∀ s : 𝓞 K, s ∉ w.asIdeal → algebraMap (𝓞 K) K s ≠ 0 := by
    intro s hs h0
    apply hs
    have : s = 0 := by simpa using h0
    rw [this]; exact w.asIdeal.zero_mem

  have hmem1 : ∀ i, y'' i ∈ Submodule.span K (Set.range y) := by
    intro i
    obtain ⟨s, hs, hsL⟩ := hlw.1 i
    have h1 : s • y'' i ∈ Submodule.span K (Set.range y) := by
      rw [← hspan]; exact Submodule.subset_span hsL
    have h2 : y'' i = (algebraMap (𝓞 K) K s)⁻¹ • (s • y'' i) := by
      rw [← algebraMap_smul K s (y'' i), smul_smul, inv_mul_cancel₀ (hs0 s hs), one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  have hmem2 : ∀ i, y i ∈ Submodule.span K (Set.range y'') := by
    intro i
    obtain ⟨s, hs, hsL⟩ := hlw.2 (y i) (hyL i)
    have h1 : s • y i ∈ Submodule.span K (Set.range y'') :=
      Submodule.span_subset_span (𝓞 K) K _ hsL
    have h2 : y i = (algebraMap (𝓞 K) K s)⁻¹ • (s • y i) := by
      rw [← algebraMap_smul K s (y i), smul_smul, inv_mul_cancel₀ (hs0 s hs), one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  have hsp : Submodule.span K (Set.range y'') = Submodule.span K (Set.range y) :=
    le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 hmem1))
      (Submodule.span_le.2 (Set.range_subset_iff.2 hmem2))
  have hdd : d'' = d := by
    have a1 := finrank_span_eq_card hy''
    have a2 := finrank_span_eq_card hy
    rw [hsp, a2] at a1
    simpa using a1.symm
  subst hdd

  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun K).1 (hmem1 j)
  set P : Matrix (Fin d'') (Fin d'') K := Matrix.of fun k j => c j k with hPdef
  have hP : ∀ j, ∑ k, P k j • y k = y'' j := fun j => hc j
  have hgram : (Matrix.of fun i j => h (y'' i) (y'' j)) =
      P.conjTranspose * (Matrix.of fun i j => h (y i) (y j)) * P := by
    ext i j
    simp only [Matrix.of_apply]
    rw [← hP i, ← hP j]
    simp only [Matrix.of_apply, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, starRingEnd_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Finset.mul_sum, Finset.sum_mul, RingHom.id_apply]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hdet : (Matrix.of fun i j => h (y'' i) (y'' j)).det =
      star P.det * (Matrix.of fun i j => h (y i) (y j)).det * P.det := by
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  have hG1 := (hG K A e n h hyp d'' y hy).1
  have hG2 := (hG K A e n h hyp d'' y'' hy'').1
  have hP0 : P.det ≠ 0 := by
    intro h0; apply hG2; rw [hdet, h0]; simp
  have hsP0 : star P.det ≠ 0 := by simpa using hP0

  have hOy : Submodule.span K ((Submodule.span (𝓞 K) (Set.range y) : Submodule (𝓞 K) A.V) : Set A.V)
      = Submodule.span K (Set.range y) := Submodule.span_span_of_tower _ _ _
  have hOy'' : Submodule.span K ((Submodule.span (𝓞 K) (Set.range y'') : Submodule (𝓞 K) A.V) :
      Set A.V) = Submodule.span K (Set.range y) := by
    rw [Submodule.span_span_of_tower]; exact hsp
  have hfg1 : (Submodule.span (𝓞 K) (Set.range y)).FG := Submodule.fg_span (Set.finite_range _)
  have hfg2 : (Submodule.span (𝓞 K) (Set.range y'')).FG := Submodule.fg_span (Set.finite_range _)
  have hy''eq : (Set.range fun j => ∑ k, P k j • y k) = Set.range y'' := by
    congr 1; funext j; exact hP j
  have hidx : ∀ u ∈ ({w, w''} : Set (HeightOneSpectrum (𝓞 K))),
      lidx u.asIdeal (Submodule.span (𝓞 K) (Set.range y)) L = vAdd u P.det := by
    intro u hu
    have hlu := hloc u hu
    rw [lidx_add_of_span_eq' (K := K) u.asIdeal _ (Submodule.span (𝓞 K) (Set.range y'')) L hfg1
      hfg2 hLfg (hOy.trans hOy''.symm) (hOy''.trans hspan.symm)]
    have z1 : lidx u.asIdeal (Submodule.span (𝓞 K) (Set.range y''))
        L = 0 := by
      apply lidx_zero_of_loc
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hlu.1 i
      · intro z hz
        exact hlu.2 z hz
    rw [z1, add_zero, ← hy''eq, lidx_span_act u y hy P hP0]
  rw [hidx w (Set.mem_insert _ _), hidx w'' (Set.mem_insert_of_mem _ rfl), hdet,
    vAdd_mul' w (mul_ne_zero hsP0 hG1) hP0, vAdd_mul' w hsP0 hG1, ← hw'' P.det]
  ring
end PI.DvRows
