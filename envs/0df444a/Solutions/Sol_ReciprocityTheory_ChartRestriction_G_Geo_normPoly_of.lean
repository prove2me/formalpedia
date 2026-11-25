-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.normPoly_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:54.963789+00:00
-- url     : https://prove2.me/submissions/616953f8-a35e-4a79-b81b-b16a6de9aaab

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeO
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_eq_zero_of_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_homog_of_cone
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_diag_of_homog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_psiPoly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_smul_homog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_monic_rel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isWeightedHomogeneous_map_of_isMultiHomog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mcPts_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (hM : PCMinContractStatement) : NormPolyStatement := by
  intro K _ ι _ P e Ψ f a hP hΨ hf hfP
  classical
  have hPp : P.IsPrime := hP.2.1.1
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  obtain ⟨k1⟩ := hP.1
  choose i hi using hP.2.1.2.2
  set d := ∑ k, a k with hd
  set g : MRing ι := ∏ k, X ⟨k, i k⟩ ^ (d - a k) with hgdef
  set f' : MRing ι := f * g with hf'def
  have hgP : g ∉ P := fun h' => by
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hPp)).mp h'
    exact hi k (hPp.mem_of_pow_mem _ hk)
  have hf'P : f' ∉ P := fun h' => (hPp.mem_or_mem h').elim hfP hgP
  have hf'h : IsWeightedHomogeneous (blkW ι) (map (Int.castRingHom ℂ) f') (fun _ => d) := by
    have h1 : IsWeightedHomogeneous (blkW ι) (map (Int.castRingHom ℂ) f) a :=
      isWeightedHomogeneous_map_of_isMultiHomog hf
    have h2 : IsWeightedHomogeneous (blkW ι) (map (Int.castRingHom ℂ) g)
        (∑ k, (d - a k) • blkW ι ⟨k, i k⟩) := by
      rw [hgdef, map_prod]
      refine IsWeightedHomogeneous.prod _ _ _ fun k _ => ?_
      rw [map_pow, map_X]
      exact (isWeightedHomogeneous_X ℂ _ _).pow _
    have hw : a + ∑ k, (d - a k) • blkW ι ⟨k, i k⟩ = fun _ => d := by
      funext k'
      have hle : a k' ≤ d := Finset.single_le_sum (fun k _ => Nat.zero_le (a k))
        (Finset.mem_univ k')
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, blkW, Pi.single_apply,
        smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      omega
    rw [hf'def, map_mul, ← hw]
    exact h1.mul h2
  obtain ⟨F, -, hF⟩ := diag_of_homog d hf'h
  obtain ⟨n, c, hcn, hrelF⟩ := exists_monic_rel Ψ P hPh hΨ F
  have hex : ∃ k, c k ≠ 0 := ⟨n, by rw [hcn]; exact one_ne_zero⟩
  set k0 := Nat.find hex with hk0def
  have hk0 : c k0 ≠ 0 := Nat.find_spec hex
  have hlt : ∀ j < k0, c j = 0 := fun j hj => by
    by_contra h
    exact Nat.find_min hex hj h
  have hk0n : k0 ≤ n := Nat.find_min' hex (by rw [hcn]; exact one_ne_zero)
  set S := (Finset.range (n + 1)).filter (fun j => k0 ≤ j) with hSdef
  set H : MRingOver ℂ ι := ∑ j ∈ S,
    bind₁ (psiPoly Ψ) (c j) * (map (Int.castRingHom ℂ) f') ^ (j - k0) with hHdef
  have hbind : ∀ (z : (Σ k, ι k) → ℂ) (q : MvPolynomial (Fin (e + 1)) ℂ),
      eval z (bind₁ (psiPoly Ψ) q) = eval (Ψ (segre z)) q := by
    intro z q
    induction q using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
    | mul_X p j hp => rw [map_mul, map_mul, hp, bind₁_X_right, eval_psiPoly, map_mul, eval_X]
  have hevalH : ∀ z, eval z H = ∑ j ∈ S, eval (Ψ (segre z)) (c j) * eval (segre z) F ^ (j - k0) := by
    intro z
    rw [hHdef, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, hbind, hF]
  have hmul : ∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) (f' ^ k0)) * eval z H = 0 := by
    intro z hz
    rw [hevalH, map_pow, map_pow, hF, Finset.mul_sum, ← hrelF z hz]
    rw [hSdef, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : k0 ≤ j
    · rw [if_pos hj]
      rw [show j = k0 + (j - k0) from (Nat.add_sub_cancel' hj).symm]
      rw [Nat.add_sub_cancel_left, pow_add]
      ring
    · rw [if_neg hj, hlt j (not_le.mp hj), map_zero, zero_mul]
  have hH := eval_eq_zero_of_mul hM hP (u := f' ^ k0) (fun h' => hf'P (hPp.mem_of_pow_mem _ h'))
    hmul
  set T : Set (Fin (e + 1) → ℂ) :=
    {v | ∃ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) f) = 0 ∧ Ψ (segre z) = v} with hTdef
  have hcT : ∀ v ∈ T, eval v (c k0) = 0 := by
    rintro _ ⟨z, hz, hfz, rfl⟩
    have h0 := hH z hz
    have hF0 : eval (segre z) F = 0 := by
      rw [← hF, hf'def, map_mul, map_mul, hfz, zero_mul]
    rw [hevalH, hF0] at h0
    rw [Finset.sum_eq_single k0] at h0
    · simpa using h0
    · intro j hj hjk
      have : 0 < j - k0 := by
        have := (Finset.mem_filter.mp hj).2
        omega
      rw [zero_pow this.ne', mul_zero]
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), le_rfl⟩) h
  have hT : ∀ v ∈ T, ∀ t : ℂ, t ≠ 0 → (fun j => t * v j) ∈ T := by
    rintro _ ⟨z, hz, hfz, rfl⟩ t ht
    set cc : K → ℂ := Function.update (fun _ => (1 : ℂ)) k1 t with hccdef
    have hcc : ∀ k, cc k ≠ 0 := by
      intro k
      by_cases hk : k = k1
      · subst hk; simp [hccdef, ht]
      · simp [hccdef, Function.update_of_ne hk]
    have hpc : ∏ k, cc k = t := by
      simp [hccdef, Finset.prod_update_of_mem (Finset.mem_univ k1)]
    refine ⟨fun p => cc p.1 * z p, mcPts_smul hPh cc hcc hz, ?_, ?_⟩
    · rw [eval_smul_homog f a hf cc z, hfz, mul_zero]
    · rw [segre_smul, map_smul, hpc]
      rfl
  obtain ⟨m, hm0, hmh, hmT⟩ := exists_homog_of_cone hk0 hT hcT
  exact ⟨homogeneousComponent m (c k0), m, hm0, hmh, fun z hz hfz => hmT _ ⟨z, hz, hfz, rfl⟩⟩
end ReciprocityTheory.ChartRestriction.G.Geo
