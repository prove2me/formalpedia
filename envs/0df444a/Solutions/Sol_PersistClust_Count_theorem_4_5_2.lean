-- Prove2me | solution 2 for PersistClust.Count.theorem_4_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-09T11:31:07.431215+00:00
-- url     : https://prove2.me/submissions/6242882e-3f26-481c-be78-273b8b5ee67e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Theorems.Thm_PersistClust_Count_theorem_4_5_lemma_4_6_corrected
import Theorems.Thm_PersistClust_Count_theorem_4_5_interleaving_corrected

open Bundle
open scoped ContDiff Manifold

/-!
# Theorem 4.5 — reduction to the corrected Lemma 4.6 and the corrected geometric interleaving

The proof of Theorem 4.5 (RR-6968, p. 21) factors into two independent ingredients, here given in
their **corrected** form (the previously published pair was falsified by counterexamples on
$X = \mathbb R$).

1. **Lemma 4.6 (algebraic stability above `α`), corrected.** For two genuine 0-dimensional
   persistence rank functions — i.e. rank functions of filtrations obeying `FiltrationLaw` — that are
   strongly `ε`-interleaved above `α` in the **box-expansion** rank form
   $r_X(s,t) \le r_Y(s-\varepsilon, t+\varepsilon)$ (and the symmetric inequality), valid for
   $s \ge t + 2\varepsilon$ with $t \ge \alpha$, the multi-bijection of assertions (i)–(iv) exists.
   This is `theorem_4_5_lemma_4_6_corrected`. The `FiltrationLaw` hypothesis is essential: with only
   rank inequalities (even box-expansion) an arbitrary non-monotone rank function can satisfy them and
   still violate the conclusion (a Lean-verified counterexample).

2. **Geometric interleaving, corrected.** Under the hypotheses of Theorem 4.5 the superlevel-set
   filtration and the upper-star Rips filtration are strongly $c\delta$-interleaved above $\alpha$.
   The interleaving maps factor through $x_{s,t} = \psi_{t+\varepsilon} \circ y_{s-\varepsilon,
   t+\varepsilon} \circ \varphi_s$ (valid for $\beta \ge \alpha$), which yields the box-expansion rank
   inequalities with $\varepsilon = c\delta$, together with the structural `FiltrationLaw` facts and
   the diagram-like / finite-support tameness facts. This is
   `theorem_4_5_interleaving_corrected`.

Setting $r_X = $ `superRank f`, $r_Y = $ `ripsRank … δ` and $\varepsilon = c\delta$, the two diagrams
`diagram0 f = mult (superRank f)` and `ripsDiagram … δ = mult (ripsRank … δ)` are definitionally
`mult r_X` and `mult r_Y`, so the conclusion of the algebraic lemma is definitionally the goal of
Theorem 4.5.
-/

open PersistClust.Count

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {X : Type*} [MetricSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
    [RiemannianBundle (fun x : X ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : X ↦ TangentSpace I x)]
    [IsRiemannianManifold I X]
    (hconv : 0 < convexityRadius X)
    (L : Finset X) (f : X → ℝ) (c : ℝ) (hc : 0 ≤ c) (hLip : ∀ x y, |f x - f y| ≤ c * dist x y)
    (htame : IsTame0 f)
    (δ : ℝ) (hδ : 0 < δ) (hδρ : ENNReal.ofReal δ < convexityRadius X)
    (α : ℝ) (hL : IsGeodesicSample (L : Set X) (superlevel f α) (δ / 4)) :
    ∃ γ : Copies (diagram0 f) ≃
        Copies (ripsDiagram (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ),
      SatisfiesIIV γ α (c * δ) := by
  -- Geometric ingredient: both filtrations are genuine persistence modules (FiltrationLaw), their
  -- diagrams are diagram-like with finite support, and they are cδ-interleaved above α in the
  -- box-expansion rank form.
  obtain ⟨hLawX, hLawY, hDiagX, hDiagY, hFinX, hFinY, hbx⟩ :=
    theorem_4_5_interleaving_corrected (E := E) (H := H) (I := I) (X := X)
      hconv L f c hc hLip htame δ hδ hδρ α hL
  -- The radius ε = cδ is nonnegative.
  have hε : 0 ≤ c * δ := mul_nonneg hc (le_of_lt hδ)
  -- Algebraic ingredient (Lemma 4.6, corrected): the box-expansion interleaving above α, applied to
  -- the genuine filtration rank functions superRank f and ripsRank … δ, yields the multi-bijection.
  -- Since diagram0 f ≡ mult (superRank f) and ripsDiagram … δ ≡ mult (ripsRank … δ) definitionally,
  -- and superRank f ≡ rankFn (superlevel f) (fun t => JoinedIn (superlevel f t)),
  -- ripsRank … δ ≡ rankFn (fun t => {i | t ≤ f i}) (ripsJoined … δ), the conclusion of the lemma is
  -- definitionally the goal of Theorem 4.5.
  exact theorem_4_5_lemma_4_6_corrected
      (stageX := superlevel f) (JX := fun t => JoinedIn (superlevel f t))
      (stageY := fun t => {i | t ≤ (fun x : L => f x) i})
      (JY := ripsJoined (fun x y : L => dist (x : X) (y : X)) (fun x : L => f x) δ)
      α (c * δ) hε hLawX hLawY hbx hDiagX hDiagY hFinX hFinY
