-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.prod_one_add_eq_of_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:23:36.638674+00:00
-- url     : https://prove2.me/submissions/622d3f29-2ded-4b38-9787-e7a2460ee092

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ι : Type} [DecidableEq ι] (S : Finset ι) :
    ∀ (R : Type) [CommRing R] [Algebra ℂ R] (a : ι → ℂ) (_ : Set.InjOn a S) (g : ι → R)
      (_ : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → (a t - a s) • (g t * g s) = g t - g s),
      ∏ s ∈ S, (1 + g s) =
        1 + ∑ s ∈ S, (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) • g s := by
  refine Finset.induction_on S ?_ ?_
  · intro R _ _ a _ g _
    simp
  · intro t S ht ih R _ _ a ha g hg
    have hinj : ∀ x ∈ insert t S, ∀ y ∈ insert t S, a x = a y → x = y :=
      fun x hx y hy h => ha (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) h
    have haS : Set.InjOn a ↑S := fun x hx y hy h =>
      hinj x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) h
    have hne : ∀ s ∈ S, a t - a s ≠ 0 := fun s hs h =>
      ht ((hinj t (Finset.mem_insert_self t S) s (Finset.mem_insert_of_mem hs) (sub_eq_zero.mp h)) ▸ hs)
    have hgS : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → (a s' - a s) • (g s' * g s) = g s' - g s :=
      fun s hs s' hs' h => hg s (Finset.mem_insert_of_mem hs) s' (Finset.mem_insert_of_mem hs') h
    have hC : ∏ s ∈ S, (1 + 1 / (a t - a s)) = 1 + ∑ s ∈ S, (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) • (1 / (a t - a s)) :=
      ih ℂ a haS (fun s => 1 / (a t - a s)) (fun s hs s' hs' _ => by
        have h1 := hne s hs
        have h2 := hne s' hs'
        simp only [smul_eq_mul]
        field_simp
        ring)
    have hR := ih R a haS g hgS
    have hts : ∀ s ∈ S, g t * g s = (1 / (a t - a s)) • (g t - g s) := by
      intro s hs
      have h' := hg s (Finset.mem_insert_of_mem hs) t (Finset.mem_insert_self t S) (fun h => ht (h ▸ hs))
      rw [← h', smul_smul, one_div, inv_mul_cancel₀ (hne s hs), one_smul]
    have hcs : ∀ s ∈ S, (∏ s' ∈ (insert t S).erase s, (a s - a s' + 1) / (a s - a s')) =
        (a s - a t + 1) / (a s - a t) * (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) := by
      intro s hs
      have hst : t ≠ s := fun h => ht (h ▸ hs)
      rw [Finset.erase_insert_of_ne hst, Finset.prod_insert (fun h => ht (Finset.mem_of_mem_erase h))]
    have hct : ∏ s' ∈ S, (a t - a s' + 1) / (a t - a s') =
        1 + ∑ s ∈ S, (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) * (1 / (a t - a s)) := by
      calc ∏ s' ∈ S, (a t - a s' + 1) / (a t - a s') = ∏ s ∈ S, (1 + 1 / (a t - a s)) :=
            Finset.prod_congr rfl fun s hs => by
              have := hne s hs
              field_simp
        _ = _ := by rw [hC]; simp only [smul_eq_mul]
    have hper : ∀ s ∈ S, ((a s - a t + 1) / (a s - a t) * (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s'))) • g s =
        (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) • g s - ((∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) * (1 / (a t - a s))) • g s := by
      intro s hs
      rw [← sub_smul]
      congr 1
      have h1 := hne s hs
      have h2 : a s - a t ≠ 0 := fun h => h1 (by linear_combination -h)
      field_simp
      ring
    have hmul : ∀ s ∈ S, g t * ((∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) • g s) =
        ((∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) * (1 / (a t - a s))) • g t - ((∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s')) * (1 / (a t - a s))) • g s := by
      intro s hs
      rw [mul_smul_comm, hts s hs, smul_smul, smul_sub]
    have hsum2 : ∑ s ∈ S, (∏ s' ∈ (insert t S).erase s, (a s - a s' + 1) / (a s - a s')) • g s =
        ∑ s ∈ S, ((a s - a t + 1) / (a s - a t) * (∏ s' ∈ S.erase s, (a s - a s' + 1) / (a s - a s'))) • g s :=
      Finset.sum_congr rfl fun s hs => by rw [hcs s hs]
    rw [Finset.prod_insert ht, hR, Finset.sum_insert ht, Finset.erase_insert ht, hsum2, hct, Finset.sum_congr rfl hper, add_mul,
      one_mul, mul_add, mul_one, Finset.mul_sum, Finset.sum_congr rfl hmul, add_smul, one_smul,
      Finset.sum_smul]
    simp only [Finset.sum_sub_distrib]
    abel
end ReciprocityTheory.ChartRestriction.DS
