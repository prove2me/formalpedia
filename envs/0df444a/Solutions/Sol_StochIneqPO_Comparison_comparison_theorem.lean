-- Prove2me | solution 1 for StochIneqPO.Comparison.comparison_theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T17:34:54.310406+00:00
-- url     : https://prove2.me/submissions/1e912b67-1158-4f61-8697-04509d020d69
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE
import Definitions.Def_StochIneqPO_Comparison_iterProd
import Theorems.Thm_StochIneqPO_Comparison_theorem1_tfae
import Theorems.Thm_StochIneqPO_Comparison_prop1_iterProd_le
import Theorems.Thm_StochIneqPO_Comparison_prop2_le_of_marginals_le

open MeasureTheory ProbabilityTheory Finset StochIneqPO.Comparison

theorem solution {E : ℕ → Type*} [∀ n, TopologicalSpace (E n)]
    [∀ n, PolishSpace (E n)] [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)]
    [∀ n, PartialOrder (E n)] [∀ n, OrderClosedTopology (E n)]
    (P₁ Q₁ : Measure (E 0)) [IsProbabilityMeasure P₁] [IsProbabilityMeasure Q₁]
    (p q : (n : ℕ) → Kernel (Π i : Iic n, E i) (E (n + 1)))
    [∀ n, IsMarkovKernel (p n)] [∀ n, IsMarkovKernel (q n)]
    (hPQ : StochLE P₁ Q₁)
    (hpq : ∀ n, ∀ x y : Π i : Iic n, E i, x ≤ y → StochLE (p n x) (q n y)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
      ∃ (X Y : (n : ℕ) → Ω → E n), (∀ n, Measurable (X n)) ∧ (∀ n, Measurable (Y n)) ∧
        μ.map (fun ω n => X n ω) = Kernel.trajMeasure P₁ p ∧
        μ.map (fun ω n => Y n ω) = Kernel.trajMeasure Q₁ q ∧
        ∀ᵐ ω ∂μ, ∀ n, X n ω ≤ Y n ω := by
  -- marginals of the Ionescu-Tulcea measure are the iterated products
  have hmarg : ∀ (R : Measure (E 0)) [IsProbabilityMeasure R]
      (k : (n : ℕ) → Kernel (Π i : Iic n, E i) (E (n + 1))) [∀ n, IsMarkovKernel (k n)] (m : ℕ),
      (Kernel.trajMeasure R k).map (Preorder.frestrictLe m) = iterProd R k m := by
    intro R _ k _ m
    rw [Kernel.trajMeasure, iterProd, Measure.map_comp _ _ (by fun_prop),
      Kernel.traj_map_frestrictLe]
    rfl
  have hle : StochLE (Kernel.trajMeasure P₁ p) (Kernel.trajMeasure Q₁ q) := by
    apply prop2_le_of_marginals_le
    intro i
    rw [hmarg, hmarg]
    exact prop1_iterProd_le P₁ Q₁ p q i hPQ (fun n _ => hpq n)
  have hT := (theorem1_tfae (Kernel.trajMeasure P₁ p) (Kernel.trajMeasure Q₁ q)).out 0 3
  obtain ⟨Ω, mΩ, μ, hμ, X₁, X₂, hX₁, hX₂, hae, hm₁, hm₂⟩ := hT.mp hle
  refine ⟨Ω, mΩ, μ, hμ, fun n ω => X₁ ω n, fun n ω => X₂ ω n,
    fun n => (measurable_pi_apply n).comp hX₁, fun n => (measurable_pi_apply n).comp hX₂,
    hm₁, hm₂, ?_⟩
  filter_upwards [hae] with ω h n
  exact h n
