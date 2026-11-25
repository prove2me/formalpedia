-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.exists_gen_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:07:49.110023+00:00
-- url     : https://prove2.me/submissions/ff29a67b-6a69-400c-8fe2-77af54692ac6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y : Scheme.{0}} (L : LB X)
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution (K : ℕ → Type) [∀ i, Fintype (K i)] (φ : ∀ i, K i → (Y ⟶ X)) (ε : ∀ i, K i → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) (ht : ∀ i, (t i).IsGen) (n : ℕ) :
    ∃ (K' : Type) (_ : Fintype K') (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (t' : LB.Gen (LB.LinComb L φ' ε')),
      t'.IsGen ∧
      (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U),
        ∏ k, h (φ' k) ^ ε' k = ∏ i ∈ Finset.range n, ∏ k, h (φ i k) ^ ε i k) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        val t' r z J = ∏ i ∈ Finset.range n, val (t i) r z J := by
  induction n with
  | zero =>
    refine ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen L, ?_, ?_, ?_⟩
    · rintro (i : PEmpty.{1} → L.ι) (j : PEmpty.{1} → L.ι)
      have h0 : (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 :=
        rfl
      rw [h0, one_mul]
      simp only [LB.oneGen, map_one]
    · intro U _ h
      simp
    · intro Z r z J _
      simp [val, LB.oneGen]
      exact map_one (gm r z _)
  | succ n ih =>
    obtain ⟨K', hK', φ', ε', t', ht', hprod, hval⟩ := ih
    refine ⟨K' ⊕ K n, inferInstance, Sum.elim φ' (φ n), Sum.elim ε' (ε n),
      LB.mulGen L φ' ε' (φ n) (ε n) t' (t n),
      ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen L φ' ε' (φ n) (ε n) t' (t n) ht' (ht n), ?_, ?_⟩
    · intro U _ h
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.prod_range_succ, hprod U h]
    · intro Z r z J hJ
      rw [val_mul, Finset.prod_range_succ, hval Z r z J hJ]
      exact hJ
end ReciprocityTheory.ChartRestriction.G.H1
