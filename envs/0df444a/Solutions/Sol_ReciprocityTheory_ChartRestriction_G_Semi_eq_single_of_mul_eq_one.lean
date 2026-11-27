-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.eq_single_of_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:28:20.591003+00:00
-- url     : https://prove2.me/submissions/e8bd5d2a-ad25-43b6-ad6c-06ad7e04666f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AddMonoidAlgebra
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.Semi
theorem _root_.solution {R A : Type*} [CommRing R] [IsDomain R] [AddCommMonoid A]
    [TwoUniqueSums A] {f g : AddMonoidAlgebra R A} (h : f * g = 1) :
    ∃ a b : A, a + b = 0 ∧ f.coeff a * g.coeff b = 1 ∧
      f = single a (f.coeff a) ∧ g = single b (g.coeff b) := by
  classical
  have hone0 : (1 : AddMonoidAlgebra R A).coeff 0 = 1 := by
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  have hone1 : ∀ x : A, x ≠ 0 → (1 : AddMonoidAlgebra R A).coeff x = 0 := by
    intro x hx
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single]
    simp only [Finsupp.single_apply, hx, Ne.symm hx, if_false]
  have hf : f ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact zero_ne_one h
  have hg : g ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact zero_ne_one h
  have hfs : f.coeff.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro h0
    apply hf
    apply AddMonoidAlgebra.ext
    rw [h0, AddMonoidAlgebra.coeff_zero]
  have hgs : g.coeff.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro h0
    apply hg
    apply AddMonoidAlgebra.ext
    rw [h0, AddMonoidAlgebra.coeff_zero]
  have hcard : f.coeff.support.card * g.coeff.support.card ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨p1, hp1, p2, hp2, hne, hu1, hu2⟩ := TwoUniqueSums.uniqueAdd_of_one_lt_card hlt
    rw [Finset.mem_product] at hp1 hp2
    have hc : ∀ p : A × A, p.1 ∈ f.coeff.support → p.2 ∈ g.coeff.support →
        UniqueAdd f.coeff.support g.coeff.support p.1 p.2 → p.1 + p.2 = 0 := by
      intro p hpa hpb hu
      have e1 := AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd hu
      rw [h] at e1
      by_contra hz
      rw [hone1 _ hz] at e1
      exact mul_ne_zero (Finsupp.mem_support_iff.mp hpa) (Finsupp.mem_support_iff.mp hpb) e1.symm
    have s1 := hc p1 hp1.1 hp1.2 hu1
    have s2 := hc p2 hp2.1 hp2.2 hu2
    have h12 := hu1 hp2.1 hp2.2 (s2.trans s1.symm)
    exact hne (Prod.ext h12.1 h12.2).symm
  have hc1 := hfs.card_pos
  have hc2 := hgs.card_pos
  have hcf : f.coeff.support.card = 1 := by nlinarith
  have hcg : g.coeff.support.card = 1 := by nlinarith
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcf
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcg
  have hfa : f = single a (f.coeff a) := by
    apply AddMonoidAlgebra.ext
    rw [AddMonoidAlgebra.coeff_single]
    ext x
    by_cases hx : x = a
    · subst hx
      rw [Finsupp.single_eq_same]
    · simp only [Finsupp.single_apply, hx, Ne.symm hx, if_false]
      by_contra hne
      have hmem : x ∈ f.coeff.support := Finsupp.mem_support_iff.mpr hne
      rw [ha, Finset.mem_singleton] at hmem
      exact hx hmem
  have hgb : g = single b (g.coeff b) := by
    apply AddMonoidAlgebra.ext
    rw [AddMonoidAlgebra.coeff_single]
    ext x
    by_cases hx : x = b
    · subst hx
      rw [Finsupp.single_eq_same]
    · simp only [Finsupp.single_apply, hx, Ne.symm hx, if_false]
      by_contra hne
      have hmem : x ∈ g.coeff.support := Finsupp.mem_support_iff.mpr hne
      rw [hb, Finset.mem_singleton] at hmem
      exact hx hmem
  have hu : UniqueAdd f.coeff.support g.coeff.support a b := by
    intro a' b' ha' hb' _
    rw [ha, Finset.mem_singleton] at ha'
    rw [hb, Finset.mem_singleton] at hb'
    exact ⟨ha', hb'⟩
  have e1 := AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd hu
  rw [h] at e1
  have hfa0 : f.coeff a ≠ 0 := Finsupp.mem_support_iff.mp (by rw [ha]; exact Finset.mem_singleton_self a)
  have hgb0 : g.coeff b ≠ 0 := Finsupp.mem_support_iff.mp (by rw [hb]; exact Finset.mem_singleton_self b)
  have hab : a + b = 0 := by
    by_contra hz
    rw [hone1 _ hz] at e1
    exact mul_ne_zero hfa0 hgb0 e1.symm
  rw [hab, hone0] at e1
  exact ⟨a, b, hab, e1.symm, hfa, hgb⟩
end ReciprocityTheory.ChartRestriction.G.Semi
