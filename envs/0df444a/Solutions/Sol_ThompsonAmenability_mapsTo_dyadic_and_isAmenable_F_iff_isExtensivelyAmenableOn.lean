-- Prove2me | solution 1 for ThompsonAmenability.mapsTo_dyadic_and_isAmenable_F_iff_isExtensivelyAmenableOn
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-30T19:16:59.284464+00:00
-- url     : https://prove2.me/submissions/666719da-8f0a-4c56-aa09-ac8fa41b2b02
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CannonFloydParry_bijOn_dyadic
import Theorems.Thm_ThompsonAmenability_isAmenable_F_of_isExtensivelyAmenableOn
import Definitions.Def_Garrido_Amenability
import Definitions.Def_ThompsonAmenability
import Mathlib
import Definitions.Def_CannonFloydParry

section
/-! # Amenable groups act extensively amenably

For a group `G` acting on `X` and a `G`-invariant set `Y ⊆ X`, amenability of `G` gives an
invariant mean on the finite subsets of `X` witnessing `IsExtensivelyAmenableOn G X Y`.

Construction: `ν` is the invariant finitely additive probability on `G`; `U` is an ultrafilter
on `Finset X` containing `{E | E ⊆ Y}` and every cone `{E | E₀ ⊆ E}` with `E₀ ⊆ Y` finite; and
`m S = ν {g | g • E ∈ S for U-almost every E}`. -/

namespace ThompsonAmenability.Dev.Chornyi

open scoped Pointwise

variable {G X : Type*} [Group G] [MulAction G X]

/-- The action of `g` on finite subsets of `X`, exactly as `IsExtensivelyAmenableOn` writes it. -/
def act (g : G) (E : Finset X) : Finset X := E.map (MulAction.toPerm g).toEmbedding

lemma mem_act {g : G} {E : Finset X} {x : X} : x ∈ act g E ↔ g⁻¹ • x ∈ E := by
  unfold act
  rw [Finset.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨g⁻¹ • x, h, by simp⟩

lemma act_mul (g h : G) (E : Finset X) : act (g * h) E = act g (act h E) := by
  ext x
  simp only [mem_act, mul_inv_rev, mul_smul]

lemma act_one (E : Finset X) : act (1 : G) E = E := by
  ext x
  simp only [mem_act, inv_one, one_smul]

/-- An ultrafilter on the finite subsets of `X` concentrated on the finite subsets of `Y` and
containing every cone over a finite subset of `Y`. -/
lemma exists_ultrafilter (Y : Set X) : ∃ U : Ultrafilter (Finset X),
    {E : Finset X | (E : Set X) ⊆ Y} ∈ U ∧
      ∀ E₀ : Finset X, (E₀ : Set X) ⊆ Y → {E : Finset X | E₀ ⊆ E} ∈ U := by
  classical
  let f : Finset Y → Finset X := fun s => s.map (Function.Embedding.subtype (· ∈ Y))
  let V : Ultrafilter (Finset Y) := Ultrafilter.of Filter.atTop
  refine ⟨V.map f, ?_, ?_⟩
  · rw [Ultrafilter.mem_map]
    have : f ⁻¹' {E : Finset X | (E : Set X) ⊆ Y} = Set.univ := by
      ext s
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ, iff_true, f]
      intro x hx
      rw [Finset.mem_coe, Finset.mem_map] at hx
      obtain ⟨a, -, rfl⟩ := hx
      exact a.2
    rw [this]
    exact Filter.univ_mem
  · intro E₀ hE₀
    rw [Ultrafilter.mem_map]
    apply Ultrafilter.of_le (Filter.atTop : Filter (Finset Y))
    rw [Filter.mem_atTop_sets]
    refine ⟨E₀.subtype (· ∈ Y), fun s hs => ?_⟩
    show E₀ ⊆ f s
    intro x hx
    have hxs : (⟨x, hE₀ hx⟩ : Y) ∈ s := hs (Finset.mem_subtype.2 hx)
    exact Finset.mem_map.2 ⟨_, hxs, rfl⟩

/-- The set of `g` such that `g • E ∈ S` for `U`-almost every finite set `E`. -/
def sat (U : Ultrafilter (Finset X)) (S : Set (Finset X)) : Set G :=
  {g | act g ⁻¹' S ∈ U}

lemma sat_empty (U : Ultrafilter (Finset X)) : sat (G := G) U ∅ = ∅ := by
  ext g
  simp only [sat, Set.preimage_empty, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  exact U.empty_notMem

lemma sat_univ (U : Ultrafilter (Finset X)) : sat (G := G) U Set.univ = Set.univ := by
  ext g
  simp only [sat, Set.preimage_univ, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact Filter.univ_mem

lemma sat_union (U : Ultrafilter (Finset X)) (S T : Set (Finset X)) :
    sat (G := G) U (S ∪ T) = sat U S ∪ sat U T := by
  ext g
  simp only [sat, Set.preimage_union, Set.mem_ofPred_eq, Set.mem_union]
  exact Ultrafilter.union_mem_iff

lemma sat_disjoint (U : Ultrafilter (Finset X)) {S T : Set (Finset X)} (hST : Disjoint S T) :
    Disjoint (sat (G := G) U S) (sat U T) := by
  refine Set.disjoint_left.2 fun g hS hT => ?_
  have h := Filter.inter_mem hS hT
  rw [← Set.preimage_inter, hST.inter_eq, Set.preimage_empty] at h
  exact U.empty_notMem h

lemma sat_image (U : Ultrafilter (Finset X)) (h : G) (S : Set (Finset X)) :
    sat (G := G) U (act h '' S) = h • sat (G := G) U S := by
  ext k
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
  have : act k ⁻¹' (act h '' S) = act (h⁻¹ * k) ⁻¹' S := by
    ext E
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨F, hF, hFE⟩
      have : F = act (h⁻¹ * k) E := by
        rw [act_mul, ← hFE, ← act_mul, inv_mul_cancel, act_one]
      rwa [← this]
    · intro hE
      refine ⟨act (h⁻¹ * k) E, hE, ?_⟩
      rw [← act_mul, mul_inv_cancel_left]
  simp only [sat, Set.mem_ofPred_eq, this]

/-- **Amenable groups act extensively amenably** on every invariant subset. -/
theorem isExtensivelyAmenableOn_of_isAmenable (Y : Set X)
    (hY : ∀ (g : G) (x : X), x ∈ Y → g • x ∈ Y) (hG : Garrido.IsAmenable G) :
    IsExtensivelyAmenableOn G X Y := by
  obtain ⟨ν, ⟨hν0, hνadd⟩, hν1, hνinv⟩ := hG
  obtain ⟨U, hUY, hUcone⟩ := exists_ultrafilter Y
  refine ⟨fun S => ν (sat U S), ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [sat_empty, hν0]
  · intro S T hST
    simp only [sat_union, hνadd _ _ (sat_disjoint U hST)]
  · have : sat (G := G) U {E : Finset X | (E : Set X) ⊆ Y} = Set.univ := by
      refine Set.eq_univ_of_forall fun g => ?_
      refine Filter.mem_of_superset hUY fun E hE => ?_
      intro x hx
      have := hY g _ (hE (mem_act.1 hx))
      simpa using this
    simp only [this, hν1]
  · simp only [sat_univ, hν1]
  · intro g S
    exact (congrArg ν (sat_image U g S)).trans (hνinv g _)
  · intro E₀ hE₀
    have : sat (G := G) U {E : Finset X | E₀ ⊆ E} = Set.univ := by
      refine Set.eq_univ_of_forall fun g => ?_
      have hsub : ((act g⁻¹ E₀ : Finset X) : Set X) ⊆ Y := by
        intro y hy
        have := hY g⁻¹ _ (hE₀ (mem_act.1 hy))
        simpa using this
      refine Filter.mem_of_superset (hUcone _ hsub) fun E hE => ?_
      intro x hx
      apply mem_act.2
      apply hE
      apply mem_act.2
      simpa using hx
    simp only [this, hν1]

end ThompsonAmenability.Dev.Chornyi

end

section
/-! # Elements of `F` keep the open dyadics of `(0,1)` inside `(0,1)`

The endpoint part holds for every order automorphism of `[0,1]`; the dyadic part is taken as a
hypothesis here (it is the published `CannonFloydParry.bijOn_dyadic`), so this module has no
dependency on any published theorem. -/

namespace ThompsonAmenability.Dev.Chornyi

open CannonFloydParry

/-- An order automorphism of `[0,1]` maps a point `> 0` to a point `> 0`. -/
lemma coe_apply_pos (f : UI ≃o UI) {x : UI} (hx : 0 < (x : ℝ)) : 0 < (f x : ℝ) := by
  let z0 : UI := ⟨0, le_refl _, zero_le_one⟩
  have hlt : f z0 < f x := f.strictMono (show z0 < x from hx)
  exact lt_of_le_of_lt (f z0).2.1 hlt

/-- An order automorphism of `[0,1]` maps a point `< 1` to a point `< 1`. -/
lemma coe_apply_lt_one (f : UI ≃o UI) {x : UI} (hx : (x : ℝ) < 1) : (f x : ℝ) < 1 := by
  let z1 : UI := ⟨1, zero_le_one, le_refl _⟩
  have hlt : f x < f z1 := f.strictMono (show x < z1 from hx)
  exact lt_of_lt_of_le hlt (f z1).2.2

/-- The first conjunct of the target, given that elements of `F` preserve dyadics. -/
theorem mapsTo_dyadic_of
    (hb : ∀ f : UI ≃o UI, f ∈ F →
      Set.MapsTo f {z : UI | IsDyadic (z : ℝ)} {z : UI | IsDyadic (z : ℝ)}) :
    ∀ g : F, ∀ x : UI, (0 < (x : ℝ) ∧ (x : ℝ) < 1 ∧ IsDyadic x) →
      0 < ((g • x : UI) : ℝ) ∧ ((g • x : UI) : ℝ) < 1 ∧ IsDyadic (g • x : UI) := by
  intro g x hx
  exact ⟨coe_apply_pos (g : UI ≃o UI) hx.1, coe_apply_lt_one (g : UI ≃o UI) hx.2.1,
    hb (g : UI ≃o UI) g.2 hx.2.2⟩

end ThompsonAmenability.Dev.Chornyi

end

section
namespace ThompsonAmenability

namespace Dev.Chornyi

/-- The target, from the dyadic-preservation fact `hb` and Chornyi's direction `h`. Uses no
published theorem. -/
theorem target_of
    (hb : ∀ f : CannonFloydParry.UI ≃o CannonFloydParry.UI, f ∈ CannonFloydParry.F →
      Set.MapsTo f {z : CannonFloydParry.UI | CannonFloydParry.IsDyadic (z : ℝ)}
        {z : CannonFloydParry.UI | CannonFloydParry.IsDyadic (z : ℝ)})
    (h : IsExtensivelyAmenableOn CannonFloydParry.F CannonFloydParry.UI {x : CannonFloydParry.UI | 0 < (x : ℝ) ∧ (x : ℝ) < 1 ∧ CannonFloydParry.IsDyadic x} →
      Garrido.IsAmenable CannonFloydParry.F) :
    (∀ g : CannonFloydParry.F, ∀ x : CannonFloydParry.UI, (0 < (x : ℝ) ∧ (x : ℝ) < 1 ∧ CannonFloydParry.IsDyadic x) →
      0 < ((g • x : CannonFloydParry.UI) : ℝ) ∧ ((g • x : CannonFloydParry.UI) : ℝ) < 1 ∧ CannonFloydParry.IsDyadic (g • x : CannonFloydParry.UI)) ∧
    (Garrido.IsAmenable CannonFloydParry.F ↔
      IsExtensivelyAmenableOn CannonFloydParry.F CannonFloydParry.UI {x : CannonFloydParry.UI | 0 < (x : ℝ) ∧ (x : ℝ) < 1 ∧ CannonFloydParry.IsDyadic x}) := by
  have hmaps := mapsTo_dyadic_of hb
  exact ⟨hmaps, ⟨isExtensivelyAmenableOn_of_isAmenable _ (fun g x hx => hmaps g x hx), h⟩⟩

end Dev.Chornyi

end ThompsonAmenability
end

open ThompsonAmenability in
theorem solution :
    (∀ g : CannonFloydParry.F, ∀ x : CannonFloydParry.UI, (0 < (x : ℝ) ∧ (x : ℝ) < 1 ∧ CannonFloydParry.IsDyadic x) →
      0 < ((g • x : CannonFloydParry.UI) : ℝ) ∧ ((g • x : CannonFloydParry.UI) : ℝ) < 1 ∧ CannonFloydParry.IsDyadic (g • x : CannonFloydParry.UI)) ∧
    (Garrido.IsAmenable CannonFloydParry.F ↔
      IsExtensivelyAmenableOn CannonFloydParry.F CannonFloydParry.UI {x : CannonFloydParry.UI | 0 < (x : ℝ) ∧ (x : ℝ) < 1 ∧ CannonFloydParry.IsDyadic x}) :=
  Dev.Chornyi.target_of (fun _ hf => (CannonFloydParry.bijOn_dyadic hf).mapsTo)
    isAmenable_F_of_isExtensivelyAmenableOn
