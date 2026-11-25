-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.span_embV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:27:48.076486+00:00
-- url     : https://prove2.me/submissions/06ad753c-153b-47e0-89a1-50760aaff5bf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealPlaceEmbeddings_qb_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealPlaceEmbeddings_span_real_embeddings_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings
open NumberField Module Submodule
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings
theorem _root_.solution {ι : Type} [Fintype ι] (g : Basis ι ℤ X.Λ) :
    span ℝ (Set.range fun i => X.embV (g i : Fin r → E)) = ⊤ := by
  set S := span ℝ (Set.range fun i => X.embV (g i : Fin r → E)) with hS
  have h1 : ∀ v : Fin r → E, X.embV v ∈ S := by
    intro v
    have hv : X.embV v = ∑ i, (((qb X g).repr v i : ℚ) : ℝ) • X.embV (g i : Fin r → E) := by
      conv_lhs => rw [← (qb X g).sum_repr v]
      funext τ a
      simp only [Data.embV, Data.emb, qb_apply, Finset.sum_apply, Pi.smul_apply, Rat.smul_def,
        map_sum, map_mul, map_ratCast, Complex.real_smul, Complex.ofReal_ratCast]
    rw [hv]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (subset_span ⟨i, rfl⟩)
  rw [eq_top_iff]
  intro w _
  have hw : w = ∑ a : Fin r, Ja X a (fun τ => w τ a) := by
    funext τ b
    simp [Ja, Finset.sum_apply]
  rw [hw]
  refine Submodule.sum_mem _ fun a _ => ?_
  have hz : (fun τ : X.Ψ => w τ a) ∈ span ℝ (Set.range fun x : E => fun τ : X.Ψ => τ.1 x) := by
    rw [span_real_embeddings_eq_top]; trivial
  have h2 := Submodule.mem_map_of_mem (f := Ja X a) hz
  rw [Submodule.map_span] at h2
  refine (span_le.mpr ?_) h2
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  have h3 : Ja X a (fun τ : X.Ψ => τ.1 x) = X.embV (Pi.single a x) := by
    funext τ b
    simp only [Ja, LinearMap.coe_mk, AddHom.coe_mk, Data.embV, Data.emb, Pi.single_apply]
    split_ifs <;> simp
  rw [h3]
  exact h1 _
end ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings
