-- Prove2me | solution 1 for RiemannMasullo.elementaryPartial_descends
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T01:41:40.68388+00:00
-- url     : https://prove2.me/submissions/08d76bd3-017b-4863-893e-f8b097f646b3

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L302-L307
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzBounds
open RiemannMasullo
open scoped ContDiff ENNReal
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
theorem solution (f : ElementaryLieGroup m n r F → ℂ)
    (β : Fin m → ℕ) (γ : Fin n → ℕ) (a : Fin r → ℤ) (b : F)
    (hf : ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) :
    ContDiff ℝ ∞ (fun xt ↦ elementaryPartial f β γ xt a b) ∧
      ∀ u v, elementaryCover u a b = elementaryCover v a b →
        elementaryPartial f β γ u a b = elementaryPartial f β γ v a b := by
  let E := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let g : E → ℂ := fun z ↦ f (elementaryCover z a b)
  let dirs : List E :=
    (List.ofFn (fun i : Fin m ↦ List.replicate (β i) (EuclideanSpace.single i 1, 0))).flatten ++
    (List.ofFn (fun i : Fin n ↦ List.replicate (γ i) (0, EuclideanSpace.single i 1))).flatten
  change ContDiff ℝ ∞ (fun z ↦ iteratedFDeriv ℝ dirs.length g z dirs.get) ∧ _
  constructor
  · exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin dirs.length ↦ E) ℂ dirs.get).contDiff.comp
      (hf.iteratedFDeriv_right (m := ∞) (i := dirs.length) (by
        change (↑((⊤ : ℕ∞) + (dirs.length : ℕ∞)) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
        exact_mod_cast (le_top : (⊤ : ℕ∞) + (dirs.length : ℕ∞) ≤ ⊤)))
  intro u v huv
  have hx : u.1 = v.1 := congrArg (fun z : ElementaryLieGroup m n r F ↦ z.1) huv
  have ht (i : Fin n) : (u.2 i : AddCircle (1 : ℝ)) = (v.2 i : AddCircle (1 : ℝ)) :=
    congrArg (fun z : ElementaryLieGroup m n r F ↦ z.2.1 i) huv
  have hperiod : (fun z : E ↦ g ((v - u) + z)) = g := by
    funext z
    apply congrArg f
    apply Prod.ext
    · change (v.1 - u.1) + z.1 = z.1
      simp [hx]
    refine Prod.ext ?_ (by rfl)
    funext i
    change ((v.2 i - u.2 i + z.2 i : ℝ) : AddCircle (1 : ℝ)) = _
    rw [AddCircle.coe_add, AddCircle.coe_sub, ht i, sub_self, zero_add]
    rfl
  have hd := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := g) dirs.length (v-u) u
  rw [hperiod, sub_add_cancel] at hd
  exact congrArg (fun M ↦ M dirs.get) hd
