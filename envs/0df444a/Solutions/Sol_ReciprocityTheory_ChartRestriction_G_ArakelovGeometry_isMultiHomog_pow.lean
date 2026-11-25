-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:07.545321+00:00
-- url     : https://prove2.me/submissions/15f2052e-0401-41e9-a7b8-f84a3aec4386

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
private theorem isMultiHomog_mul_lemma {f g : MRing ι} {c c' : K → ℕ} (hf : IsMultiHomog f c)
    (hg : IsMultiHomog g c') : IsMultiHomog (f * g) (c + c') := by
  classical
  intro m hm k
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf a ha k, hg b hb k, Pi.add_apply]
private theorem isMultiHomog_one_arakelov_geometry : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {f : MRing ι} {c : K → ℕ} (hf : IsMultiHomog f c) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • c) := by
  induction n with
  | zero =>
    simp only [pow_zero, zero_smul]
    exact isMultiHomog_one_arakelov_geometry
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact isMultiHomog_mul_lemma ih hf
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
