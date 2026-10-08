-- Prove2me | solution 1 for ThompsonAmenability.isAmenable_iff_isExtensivelyAmenableOn_of_le_Hpp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T17:13:49.816041+00:00
-- url     : https://prove2.me/submissions/f4abe45d-a5d3-41f1-b50b-084a57944634

import Definitions.Def_Garrido_Amenability
import Definitions.Def_ThompsonAmenability
import Definitions.Def_Monod_PiecewiseProjective
import Theorems.Thm_Monod_mem_G_iff_isPiecewiseProj
import Theorems.Thm_Monod_Gpp_eq_G_top_and_Hpp_eq_H_top
import Definitions.Def_HomeomorphAction
import Definitions.Def_GermGroupoid
import Theorems.Thm_GermGroupoid_isAmenable_of_isExtensivelyAmenableOn
import Theorems.Thm_Garrido_isAmenable_of_isSolvable_of_finiteIndex
import Mathlib


section
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
end

section
section
/-!
# Changing the set of an extensively amenable action

* Adjoining a `G`-fixed point `p` to `Y` keeps extensive amenability (push the mean along
  `E ↦ insert p E`).
* Extensive amenability on `Y` gives it on any `G`-invariant `Z ⊆ Y` (push the mean along
  `E ↦ E ∩ Z`).
-/

open scoped ENNReal Pointwise

namespace FAmenHZ

section Insert

variable {G X : Type*} [Group G] [MulAction G X]

lemma fam_mono' {α : Type*} {m : Set α → ℝ≥0∞} (hm : Garrido.IsFinitelyAdditiveMeasure m)
    {s t : Set α} (hst : s ⊆ t) : m s ≤ m t := by
  have := hm.2 s (t \ s) disjoint_sdiff_self_right
  rw [Set.union_sdiff_cancel hst] at this
  rw [this]
  exact le_self_add

/-- Adjoining a `G`-fixed point `p` to `Y` keeps extensive amenability: push the mean forward
along `E ↦ insert p E`. -/
theorem isExtensivelyAmenableOn_insert [DecidableEq X] (Y : Set X) (p : X)
    (hp : ∀ g : G, g • p = p) (h : ThompsonAmenability.IsExtensivelyAmenableOn G X Y) :
    ThompsonAmenability.IsExtensivelyAmenableOn G X (insert p Y) := by
  obtain ⟨m, hm, hY, h1, hinv, hcone⟩ := h
  have hle : ∀ S, m S ≤ 1 := fun S => h1 ▸ fam_mono' hm (Set.subset_univ S)
  let act : G → Finset X → Finset X := fun g E => E.map (MulAction.toPerm g).toEmbedding
  have mem_act : ∀ g E x, x ∈ act g E ↔ g⁻¹ • x ∈ E := by
    intro g E x
    simp only [act, Finset.mem_map, Equiv.toEmbedding_apply, MulAction.toPerm_apply]
    constructor
    · rintro ⟨a, ha, rfl⟩; simpa using ha
    · intro hx; exact ⟨g⁻¹ • x, hx, by simp⟩
  have act_inv : ∀ g E, act g⁻¹ (act g E) = E := by
    intro g E; ext x; simp [mem_act]
  have act_inv' : ∀ g E, act g (act g⁻¹ E) = E := by
    intro g E; ext x; simp [mem_act]
  have act_insert : ∀ g E, act g (insert p E) = insert p (act g E) := by
    intro g E; ext x
    rw [mem_act, Finset.mem_insert, Finset.mem_insert, mem_act]
    constructor
    · rintro (h | h)
      · left; rw [← smul_inv_smul g x, h, hp]
      · right; exact h
    · rintro (h | h)
      · left; rw [h, hp]
      · right; exact h
  refine ⟨fun S => m {E | insert p E ∈ S}, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simpa using hm.1
  · intro s t hst
    have : {E : Finset X | insert p E ∈ s ∪ t} = {E | insert p E ∈ s} ∪ {E | insert p E ∈ t} := by
      ext E; simp
    simp only
    rw [this]
    exact hm.2 _ _ (Set.disjoint_left.2 fun E hs ht => Set.disjoint_left.1 hst hs ht)
  · refine le_antisymm (hle _) ?_
    rw [← hY]
    refine fam_mono' hm fun E hE => ?_
    simp only [Set.mem_ofPred_eq, Finset.coe_insert] at hE ⊢
    exact Set.insert_subset_insert hE
  · simpa using h1
  · intro g S
    simp only
    have : {E : Finset X | insert p E ∈ (fun E => E.map (MulAction.toPerm g).toEmbedding) '' S} =
        (fun E => E.map (MulAction.toPerm g).toEmbedding) '' {E | insert p E ∈ S} := by
      ext E
      simp only [Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨F, hF, hFE⟩
        refine ⟨act g⁻¹ E, ?_, act_inv' g E⟩
        have : F = act g⁻¹ (insert p E) := by
          rw [← hFE]; exact (act_inv g F).symm
        rw [this, act_insert] at hF
        exact hF
      · rintro ⟨F, hF, rfl⟩
        exact ⟨insert p F, hF, act_insert g F⟩
    rw [this]
    exact hinv g _
  · intro E₀ hE₀
    refine le_antisymm (hle _) ?_
    have hE₀' : (↑(E₀.erase p) : Set X) ⊆ Y := by
      intro x hx
      rw [Finset.coe_erase] at hx
      rcases hE₀ hx.1 with h | h
      · exact absurd h hx.2
      · exact h
    rw [← hcone _ hE₀']
    refine fam_mono' hm fun E hE => ?_
    simp only [Set.mem_ofPred_eq] at hE ⊢
    intro x hx
    by_cases hxp : x = p
    · rw [hxp]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hE (Finset.mem_erase.2 ⟨hxp, hx⟩))

end Insert

end FAmenHZ

end
end

section
section
open Filter Topology OnePoint Matrix

set_option linter.unusedSimpArgs false

namespace Monod.Dev.Alg

variable {A : Subring ℝ}

/-- The real entries of an element of `SL(2, A)`. -/
def ent (g : SpecialLinearGroup (Fin 2) A) (i j : Fin 2) : ℝ :=
  ((g : Matrix (Fin 2) (Fin 2) A) i j : ℝ)

lemma ent_det (g : SpecialLinearGroup (Fin 2) A) :
    ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_two] at h
  have := congrArg (fun t : A => (t : ℝ)) h
  simpa [ent] using this

lemma mob_infty (g : SpecialLinearGroup (Fin 2) A) :
    mob g ∞ = if ent g 1 0 = 0 then ∞ else ((ent g 0 0 / ent g 1 0 : ℝ) : OnePoint ℝ) := by
  unfold mob; rw [OnePoint.smul_infty_eq_ite]; rfl

lemma mob_coe (g : SpecialLinearGroup (Fin 2) A) (x : ℝ) :
    mob g (x : OnePoint ℝ) = if ent g 1 0 * x + ent g 1 1 = 0 then ∞ else
      (((ent g 0 0 * x + ent g 0 1) / (ent g 1 0 * x + ent g 1 1) : ℝ) : OnePoint ℝ) := by
  unfold mob; rw [OnePoint.smul_some_eq_ite]; rfl

lemma mob_mul (g h : SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    mob (g * h) x = mob g (mob h x) := by
  unfold mob; rw [map_mul, mul_smul]

lemma mob_one (x : OnePoint ℝ) : mob (1 : SpecialLinearGroup (Fin 2) A) x = x := by
  unfold mob; rw [map_one, one_smul]

lemma mob_inv_mob (g : SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    mob g⁻¹ (mob g x) = x := by
  rw [← mob_mul, inv_mul_cancel, mob_one]

lemma mob_mob_inv (g : SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    mob g (mob g⁻¹ x) = x := by
  rw [← mob_mul, mul_inv_cancel, mob_one]

/-! ### Continuity of a Möbius map -/

/-- The explicit Möbius formula. -/
noncomputable def mobF (a b c d : ℝ) (p : OnePoint ℝ) : OnePoint ℝ :=
  p.elim (if c = 0 then ∞ else ((a / c : ℝ) : OnePoint ℝ))
    (fun x => if c * x + d = 0 then ∞ else (((a * x + b) / (c * x + d) : ℝ) : OnePoint ℝ))

@[simp] lemma mobF_infty (a b c d : ℝ) :
    mobF a b c d ∞ = if c = 0 then ∞ else ((a / c : ℝ) : OnePoint ℝ) := rfl

@[simp] lemma mobF_coe (a b c d x : ℝ) :
    mobF a b c d (x : OnePoint ℝ) =
      if c * x + d = 0 then ∞ else (((a * x + b) / (c * x + d) : ℝ) : OnePoint ℝ) := rfl

lemma mob_eq_mobF (g : SpecialLinearGroup (Fin 2) A) :
    mob g = mobF (ent g 0 0) (ent g 0 1) (ent g 1 0) (ent g 1 1) := by
  funext p
  cases p with
  | infty => rw [mob_infty]; rfl
  | coe x => rw [mob_coe]; rfl

lemma tendsto_coe_cobounded {α : Type*} {l : Filter α} {φ : α → ℝ}
    (h : Tendsto φ l (Bornology.cobounded ℝ)) :
    Tendsto (fun y => (φ y : OnePoint ℝ)) l (𝓝 ∞) := by
  have := OnePoint.tendsto_coe_infty (X := ℝ)
  rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] at this
  exact this.comp h

theorem continuous_mobF {a b c d : ℝ} (hdet : a * d - b * c ≠ 0) :
    Continuous (mobF a b c d) := by
  rw [continuous_iff_continuousAt]
  intro p
  cases p with
  | infty =>
    rw [OnePoint.continuousAt_infty', coclosedCompact_eq_cocompact,
      ← Metric.cobounded_eq_cocompact]
    by_cases hc : c = 0
    · have hd : d ≠ 0 := by rintro rfl; apply hdet; simp [hc]
      have ha : a ≠ 0 := by rintro rfl; apply hdet; simp [hc]
      have hF : (mobF a b c d ∘ OnePoint.some) = fun y : ℝ => (((a / d) * y + b / d : ℝ) : OnePoint ℝ) := by
        funext y
        simp only [Function.comp, mobF_infty, mobF_coe, hc, zero_mul, zero_add, hd, if_false]
        congr 1; field_simp
      have h0 : mobF a b c d ∞ = ∞ := by simp [mobF_infty, mobF_coe, hc]
      rw [hF, h0]
      exact tendsto_coe_cobounded ((tendsto_add_const_cobounded (b / d)).comp
        (tendsto_mul_left_cobounded (div_ne_zero ha hd)))
    · have h0 : mobF a b c d ∞ = ((a / c : ℝ) : OnePoint ℝ) := by simp [mobF_infty, mobF_coe, hc]
      rw [h0]
      have hinv := tendsto_inv₀_cobounded' (α := ℝ)
      have hinv0 : Tendsto (fun y : ℝ => y⁻¹) (Bornology.cobounded ℝ) (𝓝 0) :=
        hinv.mono_right nhdsWithin_le_nhds
      have hne0 : ∀ᶠ y : ℝ in Bornology.cobounded ℝ, y⁻¹ ≠ 0 :=
        hinv.eventually (self_mem_nhdsWithin)
      have hlim : Tendsto (fun y : ℝ => (a + b * y⁻¹) / (c + d * y⁻¹)) (Bornology.cobounded ℝ)
          (𝓝 (a / c)) := by
        have h1 : Tendsto (fun y : ℝ => a + b * y⁻¹) (Bornology.cobounded ℝ) (𝓝 (a + b * 0)) :=
          tendsto_const_nhds.add (tendsto_const_nhds.mul hinv0)
        have h2 : Tendsto (fun y : ℝ => c + d * y⁻¹) (Bornology.cobounded ℝ) (𝓝 (c + d * 0)) :=
          tendsto_const_nhds.add (tendsto_const_nhds.mul hinv0)
        simp only [mul_zero, add_zero] at h1 h2
        exact h1.div h2 hc
      have hden : ∀ᶠ y : ℝ in Bornology.cobounded ℝ, c + d * y⁻¹ ≠ 0 := by
        have h2 : Tendsto (fun y : ℝ => c + d * y⁻¹) (Bornology.cobounded ℝ) (𝓝 (c + d * 0)) :=
          tendsto_const_nhds.add (tendsto_const_nhds.mul hinv0)
        simp only [mul_zero, add_zero] at h2
        exact h2.eventually_ne hc
      have hev : (fun y : ℝ => (((a + b * y⁻¹) / (c + d * y⁻¹) : ℝ) : OnePoint ℝ)) =ᶠ[Bornology.cobounded ℝ]
          (mobF a b c d ∘ OnePoint.some) := by
        filter_upwards [hne0, hden] with y hy1 hy2
        have hy : y ≠ 0 := by intro h; exact hy1 (by simp [h])
        have hcy : c * y + d ≠ 0 := by
          intro h; apply hy2
          field_simp
          linarith
        simp only [Function.comp, mobF_infty, mobF_coe, hcy, if_false]
        congr 1
        field_simp
      exact ((OnePoint.continuous_coe.tendsto _).comp hlim).congr' hev
  | coe x =>
    rw [OnePoint.continuousAt_coe]
    by_cases hx : c * x + d = 0
    · have hc : c ≠ 0 := by
        rintro rfl; apply hdet; simp at hx; simp [hx]
      have hax : a * x + b ≠ 0 := by
        intro h
        apply hdet
        have : d = -(c * x) := by linarith
        have hb : b = -(a * x) := by linarith
        rw [this, hb]; ring
      have hval : (mobF a b c d ∘ OnePoint.some) x = ∞ := by
        simp [mobF_infty, mobF_coe, hx]
      show Tendsto _ _ _
      rw [hval, ← nhdsNE_sup_pure x, tendsto_sup]
      refine ⟨?_, ?_⟩
      · -- off the pole
        have hψ : Tendsto (fun y : ℝ => (c * y + d) / (a * y + b)) (𝓝[≠] x) (𝓝[≠] 0) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨?_, ?_⟩
          · have : Tendsto (fun y : ℝ => (c * y + d) / (a * y + b)) (𝓝 x)
                (𝓝 ((c * x + d) / (a * x + b))) :=
              ((tendsto_const_nhds.mul tendsto_id).add tendsto_const_nhds).div
                ((tendsto_const_nhds.mul tendsto_id).add tendsto_const_nhds) hax
            rw [hx, zero_div] at this
            exact this.mono_left nhdsWithin_le_nhds
          · have hax' : ∀ᶠ y in 𝓝[≠] x, a * y + b ≠ 0 := by
              have : Tendsto (fun y : ℝ => a * y + b) (𝓝 x) (𝓝 (a * x + b)) :=
                (tendsto_const_nhds.mul tendsto_id).add tendsto_const_nhds
              exact (this.eventually_ne hax).filter_mono nhdsWithin_le_nhds
            filter_upwards [hax', self_mem_nhdsWithin] with y hy1 hy2
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            refine div_ne_zero ?_ hy1
            intro h
            apply hy2
            have : c * (y - x) = 0 := by linarith
            rcases mul_eq_zero.1 this with h' | h'
            · exact absurd h' hc
            · simp only [Set.mem_singleton_iff]; linarith
        have hinv := (tendsto_inv₀_nhdsNE_zero (α := ℝ)).comp hψ
        have hev : (fun y : ℝ => ((((c * y + d) / (a * y + b))⁻¹ : ℝ) : OnePoint ℝ))
            =ᶠ[𝓝[≠] x] (mobF a b c d ∘ OnePoint.some) := by
          filter_upwards [self_mem_nhdsWithin] with y hy
          have hcy : c * y + d ≠ 0 := by
            intro h
            apply hy
            have : c * (y - x) = 0 := by linarith
            rcases mul_eq_zero.1 this with h' | h'
            · exact absurd h' hc
            · simp only [Set.mem_singleton_iff]; linarith
          simp only [Function.comp, mobF_infty, mobF_coe, hcy, if_false, inv_div]
        exact (tendsto_coe_cobounded hinv).congr' hev
      · simp only [tendsto_pure_left]
        intro s hs
        show (mobF a b c d ∘ OnePoint.some) x ∈ s
        rw [hval]; exact mem_of_mem_nhds hs
    · have hev : (fun y : ℝ => (((a * y + b) / (c * y + d) : ℝ) : OnePoint ℝ))
          =ᶠ[𝓝 x] (mobF a b c d ∘ OnePoint.some) := by
        have : Tendsto (fun y : ℝ => c * y + d) (𝓝 x) (𝓝 (c * x + d)) :=
          (tendsto_const_nhds.mul tendsto_id).add tendsto_const_nhds
        filter_upwards [this.eventually_ne hx] with y hy
        simp [mobF_infty, mobF_coe, hy]
      have hval : (mobF a b c d ∘ OnePoint.some) x = (((a * x + b) / (c * x + d) : ℝ) : OnePoint ℝ) := by
        simp [mobF_infty, mobF_coe, hx]
      show Tendsto _ _ _
      rw [hval]
      refine Tendsto.congr' hev ?_
      exact (OnePoint.continuous_coe.tendsto _).comp
        (((tendsto_const_nhds.mul tendsto_id).add tendsto_const_nhds).div
          ((tendsto_const_nhds.mul tendsto_id).add tendsto_const_nhds) hx)

theorem continuous_mob (g : SpecialLinearGroup (Fin 2) A) : Continuous (mob g) := by
  rw [mob_eq_mobF]
  apply continuous_mobF
  rw [ent_det]; exact one_ne_zero

end Monod.Dev.Alg

end
end

section
section
open Filter Topology OnePoint Matrix

set_option linter.unusedSimpArgs false

namespace Monod.Dev.Alg

variable {A : Subring ℝ}

/-! ### A Möbius map is determined by its values on an infinite set -/

lemma mob_eq_self_of_three (k : SpecialLinearGroup (Fin 2) A) {x₁ x₂ x₃ : ℝ}
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    (h₁ : mob k x₁ = x₁) (h₂ : mob k x₂ = x₂) (h₃ : mob k x₃ = x₃) :
    ∀ p, mob k p = p := by
  have key : ∀ x : ℝ, mob k x = x →
      ent k 0 0 * x + ent k 0 1 = x * (ent k 1 0 * x + ent k 1 1) := by
    intro x hx
    rw [mob_coe] at hx
    split_ifs at hx with hden
    · exact absurd hx (OnePoint.infty_ne_coe x)
    · have := OnePoint.coe_injective hx
      rw [div_eq_iff hden] at this
      linarith
  have e1 := key _ h₁
  have e2 := key _ h₂
  have e3 := key _ h₃
  have hdet := ent_det k
  set a := ent k 0 0
  set b := ent k 0 1
  set c := ent k 1 0
  set d := ent k 1 1
  have f12 : (x₁ - x₂) * (c * (x₁ + x₂) + (d - a)) = 0 := by linear_combination e2 - e1
  have f13 : (x₁ - x₃) * (c * (x₁ + x₃) + (d - a)) = 0 := by linear_combination e3 - e1
  have g12 : c * (x₁ + x₂) + (d - a) = 0 :=
    (mul_eq_zero.1 f12).resolve_left (sub_ne_zero.2 h12)
  have g13 : c * (x₁ + x₃) + (d - a) = 0 :=
    (mul_eq_zero.1 f13).resolve_left (sub_ne_zero.2 h13)
  have hc : c = 0 := by
    have : c * (x₂ - x₃) = 0 := by linear_combination g12 - g13
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 h23)
  have hda : d = a := by rw [hc] at g12; linarith
  have hb : b = 0 := by rw [hc, hda] at e1; linarith
  have ha : a ≠ 0 := by
    intro h0; rw [hc, hb, h0] at hdet; norm_num at hdet
  intro p
  cases p with
  | infty => rw [mob_infty]; simp [c, hc]
  | coe x =>
    rw [mob_coe]
    have : c * x + d ≠ 0 := by rw [hc, hda]; simpa using ha
    rw [if_neg this]
    congr 1
    show (a * x + b) / (c * x + d) = x
    rw [div_eq_iff this, hc, hda, hb]; ring

lemma mob_eq_of_three (g g' : SpecialLinearGroup (Fin 2) A) {x₁ x₂ x₃ : ℝ}
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    (h₁ : mob g x₁ = mob g' x₁) (h₂ : mob g x₂ = mob g' x₂) (h₃ : mob g x₃ = mob g' x₃) :
    mob g = mob g' := by
  have hk : ∀ x : ℝ, mob g x = mob g' x → mob (g'⁻¹ * g) x = x := by
    intro x hx; rw [mob_mul, hx, mob_inv_mob]
  have := mob_eq_self_of_three (g'⁻¹ * g) h12 h13 h23 (hk _ h₁) (hk _ h₂) (hk _ h₃)
  funext p
  have h := this p
  rw [mob_mul] at h
  calc mob g p = mob g' (mob g'⁻¹ (mob g p)) := (mob_mob_inv _ _).symm
    _ = mob g' p := by rw [h]

lemma mob_eq_of_infinite (g g' : SpecialLinearGroup (Fin 2) A) {S : Set ℝ} (hS : S.Infinite)
    (h : ∀ x ∈ S, mob g x = mob g' x) : mob g = mob g' := by
  obtain ⟨x₁, hx₁, x₂, hx₂, h12⟩ := hS.nontrivial
  obtain ⟨x₃, hx₃, h3⟩ := (hS.sdiff (Set.toFinite {x₁, x₂})).nonempty
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h3
  exact mob_eq_of_three g g' h12 (Ne.symm h3.1) (Ne.symm h3.2) (h _ hx₁) (h _ hx₂) (h _ hx₃)

lemma infinite_of_eventually {l : Filter ℝ} [l.NeBot] (hl : l ≤ cofinite) {P : ℝ → Prop}
    (h : ∀ᶠ x in l, P x) : {x | P x}.Infinite :=
  Filter.frequently_cofinite_iff_infinite.1 (h.frequently.filter_mono hl)

lemma mob_eq_of_eventually (g g' : SpecialLinearGroup (Fin 2) A) {l : Filter ℝ} [l.NeBot]
    (hl : l ≤ cofinite) (h : ∀ᶠ x : ℝ in l, mob g x = mob g' x) : mob g = mob g' :=
  mob_eq_of_infinite g g' (infinite_of_eventually hl h) (fun _ hx => hx)

lemma nhdsNE_le_cofinite (x : ℝ) : 𝓝[≠] x ≤ cofinite := by
  rw [Filter.le_cofinite_iff_compl_singleton_mem]
  intro y
  by_cases hy : y = x
  · subst hy; exact self_mem_nhdsWithin
  · exact nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (Ne.symm hy))

/-! ### Germs on intervals -/

/-- `f` agrees with a Möbius map near every point outside `B`. -/
def LocMob (A : Subring ℝ) (B : Set (OnePoint ℝ)) (f : OnePoint ℝ → OnePoint ℝ) : Prop :=
  ∀ x ∉ B, ∃ g : SpecialLinearGroup (Fin 2) A, ∀ᶠ y in 𝓝 x, f y = mob g y

lemma germ_on_preconnected {B : Set (OnePoint ℝ)} {f : OnePoint ℝ → OnePoint ℝ}
    (hloc : LocMob A B f) {I : Set ℝ} (hIo : IsOpen I) (hIc : IsPreconnected I)
    (hIB : ∀ y ∈ I, (y : OnePoint ℝ) ∉ B) :
    ∃ g : SpecialLinearGroup (Fin 2) A, ∀ y ∈ I, f y = mob g y := by
  rcases I.eq_empty_or_nonempty with hI | ⟨x₀, hx₀⟩
  · exact ⟨1, by simp [hI]⟩
  obtain ⟨g₀, hg₀⟩ := hloc _ (hIB x₀ hx₀)
  have tr : ∀ {P : OnePoint ℝ → Prop} {y : ℝ}, (∀ᶠ w in 𝓝 (y : OnePoint ℝ), P w) →
      ∀ᶠ z : ℝ in 𝓝 y, P (z : OnePoint ℝ) :=
    fun h => (OnePoint.continuous_coe.tendsto _).eventually h
  set u : Set ℝ := {y | ∀ᶠ z : ℝ in 𝓝 y, f z = mob g₀ z}
  set v : Set ℝ := {y | ∃ g : SpecialLinearGroup (Fin 2) A,
    (∀ᶠ z : ℝ in 𝓝 y, f z = mob g z) ∧ mob g ≠ mob g₀}
  have hu : IsOpen u := isOpen_setOfPred_eventually_nhds
  have hv : IsOpen v := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨g, hg, hne⟩
    exact (eventually_eventually_nhds.2 hg).mono fun y' hy' => ⟨g, hy', hne⟩
  have huv : Disjoint u v := by
    rw [Set.disjoint_left]
    rintro y hyu ⟨g, hg, hne⟩
    apply hne
    refine mob_eq_of_eventually g g₀ (nhdsNE_le_cofinite y) ?_
    filter_upwards [nhdsWithin_le_nhds hyu, nhdsWithin_le_nhds hg] with z h1 h2
    rw [← h1, h2]
  have hsub : I ⊆ u ∪ v := by
    intro y hy
    obtain ⟨g, hg⟩ := hloc _ (hIB y hy)
    by_cases he : mob g = mob g₀
    · left; show ∀ᶠ z : ℝ in 𝓝 y, f z = mob g₀ z
      rw [← he]; exact tr hg
    · right; exact ⟨g, tr hg, he⟩
  have hIu := hIc.subset_left_of_subset_union hu hv huv hsub ⟨x₀, hx₀, tr hg₀⟩
  exact ⟨g₀, fun y hy => (hIu hy).self_of_nhds⟩

/-- A one-sided filter at a point: nontrivial, sees no single point, and has a basis of open
intervals. -/
def GoodSide (s : Filter ℝ) : Prop :=
  s.NeBot ∧ s ≤ cofinite ∧ ∀ P : ℝ → Prop, (∀ᶠ y in s, P y) →
    ∃ I : Set ℝ, IsOpen I ∧ IsPreconnected I ∧ I ∈ s ∧ ∀ y ∈ I, P y

lemma goodSide_nhdsGT (x : ℝ) : GoodSide (𝓝[>] x) := by
  refine ⟨inferInstance, (nhdsWithin_mono _ (fun y (hy : x < y) => ne_of_gt hy)).trans
    (nhdsNE_le_cofinite x), fun P hP => ?_⟩
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hP
  exact ⟨Set.Ioo x u, isOpen_Ioo, isPreconnected_Ioo, Ioo_mem_nhdsGT hu, hsub⟩

lemma goodSide_nhdsLT (x : ℝ) : GoodSide (𝓝[<] x) := by
  refine ⟨inferInstance, (nhdsWithin_mono _ (fun y (hy : y < x) => ne_of_lt hy)).trans
    (nhdsNE_le_cofinite x), fun P hP => ?_⟩
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hP
  exact ⟨Set.Ioo l x, isOpen_Ioo, isPreconnected_Ioo, Ioo_mem_nhdsLT hl, hsub⟩

lemma goodSide_atTop : GoodSide (atTop : Filter ℝ) := by
  refine ⟨inferInstance, atTop_le_cofinite, fun P hP => ?_⟩
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hP
  exact ⟨Set.Ioi M, isOpen_Ioi, isPreconnected_Ioi, Ioi_mem_atTop M,
    fun y hy => hM y (le_of_lt hy)⟩

lemma goodSide_atBot : GoodSide (atBot : Filter ℝ) := by
  refine ⟨inferInstance, atBot_le_cofinite, fun P hP => ?_⟩
  obtain ⟨M, hM⟩ := Filter.eventually_atBot.1 hP
  exact ⟨Set.Iio M, isOpen_Iio, isPreconnected_Iio, Iio_mem_atBot M,
    fun y hy => hM y (le_of_lt hy)⟩

lemma eventually_notMem_finite {s : Filter ℝ} (hs : s ≤ cofinite) {B : Set (OnePoint ℝ)}
    (hB : B.Finite) : ∀ᶠ y : ℝ in s, (y : OnePoint ℝ) ∉ B := by
  have : ((↑) ⁻¹' B : Set ℝ).Finite := hB.preimage (OnePoint.coe_injective.injOn)
  exact hs this.compl_mem_cofinite

/-- **One-sided germs.** A map that is locally Möbius off a finite set agrees with a single
Möbius map on one side of any point. -/
lemma germ_side {B : Set (OnePoint ℝ)} (hB : B.Finite) {f : OnePoint ℝ → OnePoint ℝ}
    (hloc : LocMob A B f) {s : Filter ℝ} (hs : GoodSide s) :
    ∃ g : SpecialLinearGroup (Fin 2) A, ∀ᶠ y : ℝ in s, f y = mob g y := by
  obtain ⟨I, hIo, hIc, hIs, hIB⟩ := hs.2.2 _ (eventually_notMem_finite hs.2.1 hB)
  obtain ⟨g, hg⟩ := germ_on_preconnected hloc hIo hIc hIB
  exact ⟨g, Filter.mem_of_superset hIs hg⟩

/-- The right side of a point of `P¹` (for `∞`, the side `-∞`). -/
def sideR (p : OnePoint ℝ) : Filter ℝ := p.elim atBot (fun x => 𝓝[>] x)

/-- The left side of a point of `P¹` (for `∞`, the side `+∞`). -/
def sideL (p : OnePoint ℝ) : Filter ℝ := p.elim atTop (fun x => 𝓝[<] x)

lemma goodSide_sideR (p : OnePoint ℝ) : GoodSide (sideR p) := by
  cases p with
  | infty => exact goodSide_atBot
  | coe x => exact goodSide_nhdsGT x

lemma goodSide_sideL (p : OnePoint ℝ) : GoodSide (sideL p) := by
  cases p with
  | infty => exact goodSide_atTop
  | coe x => exact goodSide_nhdsLT x

lemma map_coe_cocompact_le : Filter.map ((↑) : ℝ → OnePoint ℝ) (atBot ⊔ atTop) ≤ 𝓝 ∞ := by
  have := OnePoint.tendsto_coe_infty (X := ℝ)
  rwa [coclosedCompact_eq_cocompact, cocompact_eq_atBot_atTop] at this

lemma sideR_le (p : OnePoint ℝ) : Filter.map ((↑) : ℝ → OnePoint ℝ) (sideR p) ≤ 𝓝 p := by
  cases p with
  | infty => exact (Filter.map_mono le_sup_left).trans map_coe_cocompact_le
  | coe x =>
    rw [OnePoint.nhds_coe_eq]; exact Filter.map_mono nhdsWithin_le_nhds

lemma sideL_le (p : OnePoint ℝ) : Filter.map ((↑) : ℝ → OnePoint ℝ) (sideL p) ≤ 𝓝 p := by
  cases p with
  | infty => exact (Filter.map_mono le_sup_right).trans map_coe_cocompact_le
  | coe x =>
    rw [OnePoint.nhds_coe_eq]; exact Filter.map_mono nhdsWithin_le_nhds

lemma nhds_le_sides (p : OnePoint ℝ) :
    𝓝 p ≤ Filter.map ((↑) : ℝ → OnePoint ℝ) (sideL p) ⊔ Filter.map (↑) (sideR p) ⊔ pure p := by
  cases p with
  | infty =>
    rw [OnePoint.nhds_infty_eq, coclosedCompact_eq_cocompact, cocompact_eq_atBot_atTop,
      Filter.map_sup]
    show _ ≤ Filter.map _ atTop ⊔ Filter.map _ atBot ⊔ _
    exact sup_le_sup_right (le_of_eq (sup_comm _ _)) _
  | coe x =>
    rw [OnePoint.nhds_coe_eq, ← nhdsNE_sup_pure x, ← nhdsLT_sup_nhdsGT, Filter.map_sup,
      Filter.map_sup, Filter.map_pure]
    rfl

/-- The value at a point of a continuous map with a Möbius germ on one side. -/
lemma eq_mob_of_germ {f : OnePoint ℝ → OnePoint ℝ} (hf : Continuous f) {p : OnePoint ℝ}
    {s : Filter ℝ} [s.NeBot] (hsp : Filter.map ((↑) : ℝ → OnePoint ℝ) s ≤ 𝓝 p)
    {g : SpecialLinearGroup (Fin 2) A} (hg : ∀ᶠ y : ℝ in s, f y = mob g y) : f p = mob g p := by
  have h1 : Tendsto (fun y : ℝ => f y) s (𝓝 (f p)) :=
    (hf.tendsto p).comp (tendsto_map'_iff.1 hsp)
  have h2 : Tendsto (fun y : ℝ => mob g y) s (𝓝 (mob g p)) :=
    ((continuous_mob g).tendsto p).comp (tendsto_map'_iff.1 hsp)
  exact tendsto_nhds_unique (h1.congr' hg) h2

end Monod.Dev.Alg

end
end

section
section
/-!
# Piecewise `PSL(2, A)` maps lie in Monod's `G`

A map that is locally Möbius with `SL(2, A)` matrices off a finite subset of `P_A` is locally
Möbius with `SL(2, ℝ)` matrices (the same real entries) off a finite set. Hence the condition
`f ∈ Gpp` in the definition of `G A` is automatic, and `G A` is the subgroup generated by the maps
piecewise in `PSL(2, A)` with breakpoints in `P_A`.
-/

open Filter Topology

namespace Monod.Dev.GMono

open Monod

/-- An element of `SL(2, A)` viewed in `SL(2, ℝ) = SL(2, ⊤)`, with the same real entries. -/
noncomputable def toTop {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ) :=
  Matrix.SpecialLinearGroup.map (Subring.inclusion le_top) g

lemma slToGL_toTop {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    slToGL ⊤ (toTop g) = slToGL A g := by
  ext i j
  rfl

lemma mob_toTop {A : Subring ℝ} (g : Matrix.SpecialLinearGroup (Fin 2) A) (x : OnePoint ℝ) :
    mob (toTop g) x = mob g x := by
  unfold mob
  rw [slToGL_toTop]

/-- A map piecewise in `PSL(2, A)` with breakpoints in `E` is piecewise in `PSL(2, ℝ)` with
breakpoints anywhere. -/
theorem isPiecewiseProjOn_top_univ {A : Subring ℝ} {E : Set (OnePoint ℝ)}
    {f : OnePoint ℝ ≃ₜ OnePoint ℝ} (hf : IsPiecewiseProjOn A E f) :
    IsPiecewiseProjOn ⊤ Set.univ f := by
  obtain ⟨B, -, hB⟩ := hf
  refine ⟨B, Set.subset_univ _, fun x hx => ?_⟩
  obtain ⟨g, hg⟩ := hB x hx
  exact ⟨toTop g, hg.mono fun y hy => by rw [hy, mob_toTop]⟩

/-- **Monotonicity**: a map piecewise in `PSL(2, A)` with breakpoints in `P_A` lies in Monod's
`G`. -/
theorem mem_Gpp_of_isPiecewiseProj {A : Subring ℝ} {f : OnePoint ℝ ≃ₜ OnePoint ℝ}
    (hf : IsPiecewiseProj A f) : f ∈ Gpp :=
  Subgroup.subset_closure (isPiecewiseProjOn_top_univ hf)

end Monod.Dev.GMono

end
end

section
section
open Filter Topology OnePoint Matrix

set_option linter.unusedSimpArgs false

namespace Monod.Dev.Alg

variable {A : Subring ℝ}

lemma locMob_of_isPiecewiseProjOn {f : OnePoint ℝ ≃ₜ OnePoint ℝ}
    {B : Finset (OnePoint ℝ)}
    (h : ∀ x ∉ B, ∃ g : SpecialLinearGroup (Fin 2) A, ∀ᶠ y in 𝓝 x, f y = mob g y) :
    LocMob A (↑B : Set (OnePoint ℝ)) f := fun x hx => h x (by simpa using hx)

/-- Taken from the published Monod milestone (2026-09-30), so every proof using it carries that
edge; `mem_G_iff_isPiecewiseProj_direct` is the original argument. -/
theorem mem_G_iff_isPiecewiseProj' (A : Subring ℝ) (f : OnePoint ℝ ≃ₜ OnePoint ℝ) :
    f ∈ G A ↔ IsPiecewiseProj A f :=
  (Monod.mem_G_iff_isPiecewiseProj A f).trans
    ⟨fun h => h.2, fun h => ⟨Monod.Dev.GMono.mem_Gpp_of_isPiecewiseProj h, h⟩⟩

end Monod.Dev.Alg

end
end

section
section
open Filter Topology OnePoint Matrix

set_option linter.unusedSimpArgs false

namespace Monod.Dev.Alg

/-- The real part of a point of `P¹` (junk `0` at `∞`). -/
def re (p : OnePoint ℝ) : ℝ := p.elim 0 id

@[simp] lemma re_coe (x : ℝ) : re (x : OnePoint ℝ) = x := rfl

lemma coe_re {p : OnePoint ℝ} (hp : p ≠ ∞) : ((re p : ℝ) : OnePoint ℝ) = p := by
  cases p with
  | infty => exact absurd rfl hp
  | coe x => rfl

/-- The restriction to `ℝ` of a homeomorphism of `P¹`. -/
def realFn (h : OnePoint ℝ ≃ₜ OnePoint ℝ) (x : ℝ) : ℝ := re (h x)

lemma apply_coe_ne_infty {h : OnePoint ℝ ≃ₜ OnePoint ℝ} (hh : h ∞ = ∞) (x : ℝ) :
    h (x : OnePoint ℝ) ≠ ∞ := by
  intro hx
  rw [← hh] at hx
  exact OnePoint.coe_ne_infty x (h.injective hx)

lemma coe_realFn {h : OnePoint ℝ ≃ₜ OnePoint ℝ} (hh : h ∞ = ∞) (x : ℝ) :
    ((realFn h x : ℝ) : OnePoint ℝ) = h x := coe_re (apply_coe_ne_infty hh x)

lemma continuous_realFn {h : OnePoint ℝ ≃ₜ OnePoint ℝ} (hh : h ∞ = ∞) :
    Continuous (realFn h) := by
  rw [OnePoint.isOpenEmbedding_coe.isInducing.continuous_iff]
  have : ((↑) : ℝ → OnePoint ℝ) ∘ realFn h = h ∘ (↑) := funext (coe_realFn hh)
  rw [this]
  exact h.continuous.comp OnePoint.continuous_coe

lemma injective_realFn {h : OnePoint ℝ ≃ₜ OnePoint ℝ} (hh : h ∞ = ∞) :
    Function.Injective (realFn h) := by
  intro x y hxy
  have := congrArg ((↑) : ℝ → OnePoint ℝ) hxy
  rw [coe_realFn hh, coe_realFn hh] at this
  exact OnePoint.coe_injective (h.injective this)

lemma mem_H_top_fix {h : OnePoint ℝ ≃ₜ OnePoint ℝ} (hh : h ∈ H ⊤) : h ∞ = ∞ :=
  (Subgroup.mem_inf.1 hh).2

lemma mem_H_top_pw {h : OnePoint ℝ ≃ₜ OnePoint ℝ} (hh : h ∈ H ⊤) : IsPiecewiseProj ⊤ h :=
  (mem_G_iff_isPiecewiseProj' ⊤ h).1 (Subgroup.mem_inf.1 hh).1

/-- A Möbius map with determinant one is increasing where it is finite. -/
lemma mob_lt_mob {A : Subring ℝ} (g : SpecialLinearGroup (Fin 2) A) {y₁ y₂ : ℝ} (hy : y₁ < y₂)
    (hD : 0 < (ent g 1 0 * y₁ + ent g 1 1) * (ent g 1 0 * y₂ + ent g 1 1)) :
    (ent g 0 0 * y₁ + ent g 0 1) / (ent g 1 0 * y₁ + ent g 1 1) <
      (ent g 0 0 * y₂ + ent g 0 1) / (ent g 1 0 * y₂ + ent g 1 1) := by
  have hdet := ent_det g
  set a := ent g 0 0
  set b := ent g 0 1
  set c := ent g 1 0
  set d := ent g 1 1
  have hD1 : c * y₁ + d ≠ 0 := by intro h; rw [h, zero_mul] at hD; exact lt_irrefl _ hD
  have hD2 : c * y₂ + d ≠ 0 := by intro h; rw [h, mul_zero] at hD; exact lt_irrefl _ hD
  rw [← sub_pos, div_sub_div _ _ hD2 hD1]
  have : (a * y₂ + b) * (c * y₁ + d) - (c * y₂ + d) * (a * y₁ + b) = y₂ - y₁ := by
    linear_combination (y₂ - y₁) * hdet
  rw [this]
  apply div_pos (sub_pos.2 hy)
  rw [mul_comm]; exact hD

lemma strictMono_realFn {h : OnePoint ℝ ≃ₜ OnePoint ℝ} (hh : h ∈ H ⊤) :
    StrictMono (realFn h) := by
  have hinf := mem_H_top_fix hh
  rcases (continuous_realFn hinf).strictMono_of_inj (injective_realFn hinf) with h1 | h1
  · exact h1
  exfalso
  obtain ⟨B, -, hloc⟩ := mem_H_top_pw hh
  obtain ⟨x₀, hx₀⟩ := (eventually_notMem_finite (s := atTop) atTop_le_cofinite
    (Finset.finite_toSet B)).exists
  obtain ⟨g, hg⟩ := hloc _ (by simpa using hx₀)
  have hg' : ∀ᶠ y : ℝ in 𝓝 x₀, h y = mob g y := (OnePoint.continuous_coe.tendsto _).eventually hg
  have hD0 : ent g 1 0 * x₀ + ent g 1 1 ≠ 0 := by
    intro h0
    have := hg'.self_of_nhds
    rw [mob_coe, if_pos h0] at this
    exact apply_coe_ne_infty hinf x₀ this
  have hsign : ∀ᶠ y : ℝ in 𝓝 x₀,
      0 < (ent g 1 0 * x₀ + ent g 1 1) * (ent g 1 0 * y + ent g 1 1) := by
    have : Tendsto (fun y : ℝ => (ent g 1 0 * x₀ + ent g 1 1) * (ent g 1 0 * y + ent g 1 1))
        (𝓝 x₀) (𝓝 ((ent g 1 0 * x₀ + ent g 1 1) * (ent g 1 0 * x₀ + ent g 1 1))) :=
      tendsto_const_nhds.mul ((tendsto_const_nhds.mul tendsto_id).add tendsto_const_nhds)
    exact this.eventually (lt_mem_nhds (mul_self_pos.2 hD0))
  obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hg'.and hsign)
  set y₂ := (x₀ + u) / 2
  have hy₂ : y₂ ∈ Set.Ioo l u := ⟨by simp only [y₂]; linarith, by simp only [y₂]; linarith⟩
  have hlt : x₀ < y₂ := by simp only [y₂]; linarith
  obtain ⟨e₁, -⟩ := hsub ⟨hl, hu⟩
  obtain ⟨e₂, s₂⟩ := hsub hy₂
  have hD2 : ent g 1 0 * y₂ + ent g 1 1 ≠ 0 := by
    intro h0; rw [h0, mul_zero] at s₂; exact lt_irrefl _ s₂
  have v₁ : realFn h x₀ = (ent g 0 0 * x₀ + ent g 0 1) / (ent g 1 0 * x₀ + ent g 1 1) := by
    apply OnePoint.coe_injective
    rw [coe_realFn hinf, e₁, mob_coe, if_neg hD0]
  have v₂ : realFn h y₂ = (ent g 0 0 * y₂ + ent g 0 1) / (ent g 1 0 * y₂ + ent g 1 1) := by
    apply OnePoint.coe_injective
    rw [coe_realFn hinf, e₂, mob_coe, if_neg hD2]
  have := h1 hlt
  rw [v₁, v₂] at this
  exact lt_asymm this (mob_lt_mob g hlt s₂)

/-- The restriction to `ℝ` of an element of `H`, as an order isomorphism. -/
noncomputable def toOI (h : H ⊤) : ℝ ≃o ℝ where
  toFun := realFn h
  invFun := realFn (h⁻¹ : H ⊤)
  left_inv x := by
    apply OnePoint.coe_injective
    rw [coe_realFn (mem_H_top_fix (h⁻¹).2), coe_realFn (mem_H_top_fix h.2)]
    exact (h : OnePoint ℝ ≃ₜ OnePoint ℝ).symm_apply_apply x
  right_inv x := by
    apply OnePoint.coe_injective
    rw [coe_realFn (mem_H_top_fix h.2), coe_realFn (mem_H_top_fix (h⁻¹).2)]
    exact (h : OnePoint ℝ ≃ₜ OnePoint ℝ).apply_symm_apply x
  map_rel_iff' := (strictMono_realFn h.2).le_iff_le

lemma coe_toOI (h : H ⊤) (x : ℝ) :
    ((toOI h x : ℝ) : OnePoint ℝ) = (h : OnePoint ℝ ≃ₜ OnePoint ℝ) x :=
  coe_realFn (mem_H_top_fix h.2) x

/-- Restriction to `ℝ` as a group homomorphism. -/
noncomputable def ψ : H ⊤ →* (ℝ ≃o ℝ) where
  toFun := toOI
  map_one' := by
    ext x
    apply OnePoint.coe_injective
    rw [coe_toOI]; rfl
  map_mul' a b := by
    ext x
    apply OnePoint.coe_injective
    rw [coe_toOI]
    show _ = ((toOI a (toOI b x) : ℝ) : OnePoint ℝ)
    rw [coe_toOI, coe_toOI]
    rfl

lemma coe_ψ (h : H ⊤) (x : ℝ) :
    ((ψ h x : ℝ) : OnePoint ℝ) = (h : OnePoint ℝ ≃ₜ OnePoint ℝ) x := coe_toOI h x

end Monod.Dev.Alg

end
end

section
section
open Filter Topology OnePoint Matrix

set_option linter.unusedSimpArgs false

namespace Monod.Dev.Alg

variable {A : Subring ℝ}

/-! ### Linear algebra of the stabilizer of a point -/

/-- The real matrix of an element of `SL(2, A)` acting on a vector. -/
noncomputable def Mv (k : SpecialLinearGroup (Fin 2) A) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (A.subtype.mapMatrix (k : Matrix (Fin 2) (Fin 2) A)) *ᵥ v

lemma Mv_mul (k₁ k₂ : SpecialLinearGroup (Fin 2) A) (v : Fin 2 → ℝ) :
    Mv (k₁ * k₂) v = Mv k₁ (Mv k₂ v) := by
  show (A.subtype.mapMatrix ((k₁ : Matrix (Fin 2) (Fin 2) A) * (k₂ : Matrix (Fin 2) (Fin 2) A))) *ᵥ v = _
  rw [map_mul]; exact (Matrix.mulVec_mulVec _ _ _).symm

lemma Mv_one (v : Fin 2 → ℝ) : Mv (1 : SpecialLinearGroup (Fin 2) A) v = v := by
  simp [Mv]

lemma Mv_smul (k : SpecialLinearGroup (Fin 2) A) (c : ℝ) (v : Fin 2 → ℝ) :
    Mv k (c • v) = c • Mv k v := by
  simp only [Mv, Matrix.mulVec_smul]

lemma Mv_apply (k : SpecialLinearGroup (Fin 2) A) (v : Fin 2 → ℝ) :
    Mv k v = ![ent k 0 0 * v 0 + ent k 0 1 * v 1, ent k 1 0 * v 0 + ent k 1 1 * v 1] := by
  simp only [Mv, Matrix.mulVec_fin_two]
  rfl

/-- Elements having `v` as an eigenvector. -/
def Q1 (A : Subring ℝ) (v : Fin 2 → ℝ) (hv : v ≠ 0) : Subgroup (SpecialLinearGroup (Fin 2) A) where
  carrier := {k | ∃ c : ℝ, Mv k v = c • v}
  one_mem' := ⟨1, by rw [Mv_one, one_smul]⟩
  mul_mem' := by
    rintro k₁ k₂ ⟨c₁, h₁⟩ ⟨c₂, h₂⟩
    exact ⟨c₂ * c₁, by rw [Mv_mul, h₂, Mv_smul, h₁, smul_smul]⟩
  inv_mem' := by
    rintro k ⟨c, hc⟩
    have hback : Mv k⁻¹ (Mv k v) = v := by rw [← Mv_mul, inv_mul_cancel, Mv_one]
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [hc, zero_smul, show (0 : Fin 2 → ℝ) = (0 : ℝ) • (0 : Fin 2 → ℝ) by simp,
        Mv_smul, zero_smul] at hback
      exact hv hback.symm
    refine ⟨c⁻¹, ?_⟩
    rw [hc, Mv_smul] at hback
    calc Mv k⁻¹ v = c⁻¹ • (c • Mv k⁻¹ v) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • v := by rw [hback]

/-- Elements fixing the vector `v`. -/
def Q2 (A : Subring ℝ) (v : Fin 2 → ℝ) : Subgroup (SpecialLinearGroup (Fin 2) A) where
  carrier := {k | Mv k v = v}
  one_mem' := Mv_one v
  mul_mem' := by
    intro k₁ k₂ h₁ h₂
    show Mv (k₁ * k₂) v = v
    rw [Mv_mul, show Mv k₂ v = v from h₂, show Mv k₁ v = v from h₁]
  inv_mem' := by
    intro k hk
    show Mv k⁻¹ v = v
    conv_lhs => rw [← show Mv k v = v from hk]
    rw [← Mv_mul, inv_mul_cancel, Mv_one]

/-- Elements acting trivially on `P¹`. -/
def Qid (A : Subring ℝ) : Subgroup (SpecialLinearGroup (Fin 2) A) where
  carrier := {k | ∀ x, mob k x = x}
  one_mem' := mob_one
  mul_mem' := by
    intro k₁ k₂ h₁ h₂ x
    rw [mob_mul, h₂, h₁]
  inv_mem' := by
    intro k hk x
    conv_lhs => rw [← hk x]
    rw [mob_inv_mob]

lemma commutator_Q1_le (v : Fin 2 → ℝ) (hv : v ≠ 0) : ⁅Q1 A v hv, Q1 A v hv⁆ ≤ Q2 A v := by
  rw [Subgroup.commutator_le]
  intro k₁ h₁ k₂ h₂
  obtain ⟨c₁, e₁⟩ := h₁
  obtain ⟨c₂, e₂⟩ := h₂
  obtain ⟨d₁, f₁⟩ := (Q1 A v hv).inv_mem ⟨c₁, e₁⟩
  obtain ⟨d₂, f₂⟩ := (Q1 A v hv).inv_mem ⟨c₂, e₂⟩
  -- the eigenvalues of the inverses are the inverse eigenvalues
  have g₁ : d₁ * c₁ = 1 ∨ v = 0 := by
    have : Mv (k₁⁻¹ * k₁) v = v := by rw [inv_mul_cancel, Mv_one]
    rw [Mv_mul, e₁, Mv_smul, f₁, smul_smul] at this
    by_cases h : d₁ * c₁ = 1
    · exact Or.inl h
    · right
      have h2 : (c₁ * d₁ - 1) • v = 0 := by rw [sub_smul, this, one_smul, sub_self]
      rw [mul_comm] at h
      exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 h)
  have g₂ : d₂ * c₂ = 1 ∨ v = 0 := by
    have : Mv (k₂⁻¹ * k₂) v = v := by rw [inv_mul_cancel, Mv_one]
    rw [Mv_mul, e₂, Mv_smul, f₂, smul_smul] at this
    by_cases h : d₂ * c₂ = 1
    · exact Or.inl h
    · right
      have h2 : (c₂ * d₂ - 1) • v = 0 := by rw [sub_smul, this, one_smul, sub_self]
      rw [mul_comm] at h
      exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 h)
  have g₁' := g₁.resolve_right hv
  have g₂' := g₂.resolve_right hv
  show Mv (k₁ * k₂ * k₁⁻¹ * k₂⁻¹) v = v
  simp only [Mv_mul, f₁, f₂, e₁, e₂, Mv_smul, smul_smul]
  have key : ∀ t : ℝ, t = 1 → t • v = v := fun t ht => by rw [ht, one_smul]
  apply key
  linear_combination (d₂ * c₂) * g₁' + g₂'

lemma ent_mul (k₁ k₂ : SpecialLinearGroup (Fin 2) A) (i j : Fin 2) :
    ent (k₁ * k₂) i j = ent k₁ i 0 * ent k₂ 0 j + ent k₁ i 1 * ent k₂ 1 j := by
  simp [ent, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

lemma ext_ent {k₁ k₂ : SpecialLinearGroup (Fin 2) A} (h : ∀ i j, ent k₁ i j = ent k₂ i j) :
    k₁ = k₂ := by
  ext i j
  exact h i j

/-- The representative vector of a point of `P¹`. -/
def vec (p : OnePoint ℝ) : Fin 2 → ℝ := p.elim ![1, 0] (fun x => ![x, 1])

lemma vec_ne_zero (p : OnePoint ℝ) : vec p ≠ 0 := by
  cases p with
  | infty => intro h; have := congrFun h 0; simp [vec] at this
  | coe x => intro h; have := congrFun h 1; simp [vec] at this

lemma commute_of_Q2 (p : OnePoint ℝ) {k₁ k₂ : SpecialLinearGroup (Fin 2) A}
    (h₁ : k₁ ∈ Q2 A (vec p)) (h₂ : k₂ ∈ Q2 A (vec p)) : k₁ * k₂ = k₂ * k₁ := by
  have e₁ : Mv k₁ (vec p) = vec p := h₁
  have e₂ : Mv k₂ (vec p) = vec p := h₂
  have d₁ := ent_det k₁
  have d₂ := ent_det k₂
  rw [Mv_apply] at e₁ e₂
  apply ext_ent
  intro i j
  rw [ent_mul, ent_mul]
  cases p with
  | infty =>
    have a₁ := congrFun e₁ 0
    have c₁ := congrFun e₁ 1
    have a₂ := congrFun e₂ 0
    have c₂ := congrFun e₂ 1
    simp [vec] at a₁ c₁ a₂ c₂
    rw [a₁, c₁] at d₁
    rw [a₂, c₂] at d₂
    have dd₁ : ent k₁ 1 1 = 1 := by linarith
    have dd₂ : ent k₂ 1 1 = 1 := by linarith
    fin_cases i <;> fin_cases j <;> simp [a₁, c₁, a₂, c₂, dd₁, dd₂] <;> ring
  | coe x =>
    have a₁ := congrFun e₁ 0
    have c₁ := congrFun e₁ 1
    have a₂ := congrFun e₂ 0
    have c₂ := congrFun e₂ 1
    simp [vec] at a₁ c₁ a₂ c₂
    have hb₁ : ent k₁ 0 1 = x - ent k₁ 0 0 * x := by linarith
    have hd₁ : ent k₁ 1 1 = 1 - ent k₁ 1 0 * x := by linarith
    have hb₂ : ent k₂ 0 1 = x - ent k₂ 0 0 * x := by linarith
    have hd₂ : ent k₂ 1 1 = 1 - ent k₂ 1 0 * x := by linarith
    rw [hb₁, hd₁] at d₁
    rw [hb₂, hd₂] at d₂
    have ha₁ : ent k₁ 0 0 = 1 + ent k₁ 1 0 * x := by linarith
    have ha₂ : ent k₂ 0 0 = 1 + ent k₂ 1 0 * x := by linarith
    fin_cases i <;> fin_cases j <;> simp [hb₁, hd₁, hb₂, hd₂, ha₁, ha₂] <;> ring

lemma commutator_Q2_le (p : OnePoint ℝ) : ⁅Q2 A (vec p), Q2 A (vec p)⁆ ≤ Qid A := by
  rw [Subgroup.commutator_le]
  intro k₁ h₁ k₂ h₂ x
  rw [commutatorElement_def, commute_of_Q2 p h₁ h₂, mul_inv_cancel_right, mul_inv_cancel,
    mob_one]

lemma mem_Q1_of_mob_eq (k : SpecialLinearGroup (Fin 2) A) {p : OnePoint ℝ} (h : mob k p = p) :
    k ∈ Q1 A (vec p) (vec_ne_zero p) := by
  cases p with
  | infty =>
    rw [mob_infty] at h
    have hc : ent k 1 0 = 0 := by
      by_contra hc; rw [if_neg hc] at h; exact OnePoint.coe_ne_infty _ h
    refine ⟨ent k 0 0, ?_⟩
    rw [Mv_apply]
    ext i; fin_cases i <;> simp [vec, hc]
  | coe x =>
    rw [mob_coe] at h
    have hd : ent k 1 0 * x + ent k 1 1 ≠ 0 := by
      intro hd; rw [if_pos hd] at h; exact OnePoint.infty_ne_coe _ h
    rw [if_neg hd] at h
    have h2 := OnePoint.coe_injective h
    rw [div_eq_iff hd] at h2
    refine ⟨ent k 1 0 * x + ent k 1 1, ?_⟩
    rw [Mv_apply]
    ext i; fin_cases i <;> simp [vec] <;> linarith

/-! ### Germ subgroups -/

/-- Homeomorphisms preserving a filter, together with their inverses. -/
def TT (F : Filter (OnePoint ℝ)) : Subgroup (OnePoint ℝ ≃ₜ OnePoint ℝ) where
  carrier := {h | Tendsto h F F ∧ Tendsto h.symm F F}
  one_mem' := ⟨tendsto_id, tendsto_id⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨ha1.comp hb1, hb2.comp ha2⟩
  inv_mem' := by
    rintro a ⟨h1, h2⟩
    exact ⟨h2, h1⟩

lemma germ_mul {F : Filter (OnePoint ℝ)} {h₁ h₂ : OnePoint ℝ ≃ₜ OnePoint ℝ}
    {k₁ k₂ : SpecialLinearGroup (Fin 2) A} (ht : Tendsto h₂ F F)
    (e₁ : ∀ᶠ x in F, h₁ x = mob k₁ x) (e₂ : ∀ᶠ x in F, h₂ x = mob k₂ x) :
    ∀ᶠ x in F, (h₁ * h₂) x = mob (k₁ * k₂) x := by
  filter_upwards [e₂, ht.eventually e₁] with x hx2 hx1
  rw [Homeomorph.mul_apply, hx1, hx2, mob_mul]

lemma germ_inv {F : Filter (OnePoint ℝ)} {h : OnePoint ℝ ≃ₜ OnePoint ℝ}
    {k : SpecialLinearGroup (Fin 2) A} (ht : Tendsto h.symm F F)
    (e : ∀ᶠ x in F, h x = mob k x) :
    ∀ᶠ x in F, h⁻¹ x = mob k⁻¹ x := by
  filter_upwards [ht.eventually e] with y hy
  show h.symm y = mob k⁻¹ y
  rw [Homeomorph.apply_symm_apply] at hy
  calc h.symm y = mob k⁻¹ (mob k (h.symm y)) := (mob_inv_mob _ _).symm
    _ = mob k⁻¹ y := by rw [← hy]

/-- Filter-preserving homeomorphisms with a Möbius germ from `Q` along `F`. -/
def GS (F : Filter (OnePoint ℝ)) (Q : Subgroup (SpecialLinearGroup (Fin 2) A)) :
    Subgroup (OnePoint ℝ ≃ₜ OnePoint ℝ) where
  carrier := {h | h ∈ TT F ∧ ∃ k ∈ Q, ∀ᶠ x in F, h x = mob k x}
  one_mem' := ⟨(TT F).one_mem, 1, Q.one_mem, Eventually.of_forall fun x => (mob_one x).symm⟩
  mul_mem' := by
    rintro a b ⟨ha, ka, hka, ea⟩ ⟨hb, kb, hkb, eb⟩
    exact ⟨(TT F).mul_mem ha hb, ka * kb, Q.mul_mem hka hkb, germ_mul hb.1 ea eb⟩
  inv_mem' := by
    rintro a ⟨ha, ka, hka, ea⟩
    exact ⟨(TT F).inv_mem ha, ka⁻¹, Q.inv_mem hka, germ_inv ha.2 ea⟩

lemma commutator_GS_le (F : Filter (OnePoint ℝ)) (Q : Subgroup (SpecialLinearGroup (Fin 2) A)) :
    ⁅GS F Q, GS F Q⁆ ≤ GS F ⁅Q, Q⁆ := by
  rw [Subgroup.commutator_le]
  rintro a ⟨ha, ka, hka, ea⟩ b ⟨hb, kb, hkb, eb⟩
  refine ⟨?_, ka * kb * ka⁻¹ * kb⁻¹, by
    simpa [commutatorElement_def] using Subgroup.commutator_mem_commutator hka hkb, ?_⟩
  · rw [commutatorElement_def]
    exact (TT F).mul_mem ((TT F).mul_mem ((TT F).mul_mem ha hb) ((TT F).inv_mem ha))
      ((TT F).inv_mem hb)
  · rw [commutatorElement_def]
    have e1 := germ_mul hb.1 ea eb
    have e2 := germ_inv ha.2 ea
    have e3 := germ_mul ((TT F).inv_mem ha).1 e1 e2
    have e4 := germ_inv hb.2 eb
    exact germ_mul ((TT F).inv_mem hb).1 e3 e4

lemma GS_mono (F : Filter (OnePoint ℝ)) {Q Q' : Subgroup (SpecialLinearGroup (Fin 2) A)}
    (h : Q ≤ Q') : GS F Q ≤ GS F Q' := by
  rintro a ⟨ha, k, hk, e⟩
  exact ⟨ha, k, h hk, e⟩

/-! ### Sides of a fixed point -/

lemma tendsto_sideR (u : ℝ ≃o ℝ) (p : OnePoint ℝ) (hp : ∀ x : ℝ, p = x → u x = x) :
    Tendsto u (sideR p) (sideR p) := by
  cases p with
  | infty => exact u.tendsto_atBot
  | coe x =>
    have hx := hp x rfl
    show Tendsto u (𝓝[>] x) (𝓝[>] x)
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := u.continuous.tendsto x
      rw [hx] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y (hy : x < y)
      show x < u y
      rw [← hx]; exact u.strictMono hy

lemma tendsto_sideL (u : ℝ ≃o ℝ) (p : OnePoint ℝ) (hp : ∀ x : ℝ, p = x → u x = x) :
    Tendsto u (sideL p) (sideL p) := by
  cases p with
  | infty => exact u.tendsto_atTop
  | coe x =>
    have hx := hp x rfl
    show Tendsto u (𝓝[<] x) (𝓝[<] x)
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := u.continuous.tendsto x
      rw [hx] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y (hy : y < x)
      show u y < x
      rw [← hx]; exact u.strictMono hy

lemma ψ_fix {h : H ⊤} {p : OnePoint ℝ} (hp : (h : OnePoint ℝ ≃ₜ OnePoint ℝ) p = p) :
    ∀ x : ℝ, p = x → ψ h x = x := by
  rintro x rfl
  apply OnePoint.coe_injective
  rw [coe_ψ, hp]

/-- An element of `H` fixing `p`, on a side `s` of `p`. -/
lemma mem_GS_side {h : OnePoint ℝ ≃ₜ OnePoint ℝ} (hh : h ∈ H ⊤) {p : OnePoint ℝ} (hp : h p = p)
    {s : Filter ℝ} (hs : GoodSide s) (hsp : Filter.map ((↑) : ℝ → OnePoint ℝ) s ≤ 𝓝 p)
    (htend : ∀ u : H ⊤, (u : OnePoint ℝ ≃ₜ OnePoint ℝ) p = p → Tendsto (ψ u) s s) :
    h ∈ GS (Filter.map ((↑) : ℝ → OnePoint ℝ) s) (Q1 ⊤ (vec p) (vec_ne_zero p)) := by
  have hTT : ∀ u : H ⊤, (u : OnePoint ℝ ≃ₜ OnePoint ℝ) p = p →
      Tendsto (u : OnePoint ℝ ≃ₜ OnePoint ℝ) (Filter.map (↑) s) (Filter.map (↑) s) := by
    intro u hu
    rw [tendsto_map'_iff]
    have : (u : OnePoint ℝ ≃ₜ OnePoint ℝ) ∘ ((↑) : ℝ → OnePoint ℝ) = (↑) ∘ ψ u :=
      funext fun x => (coe_ψ u x).symm
    rw [this]
    exact tendsto_map.comp (htend u hu)
  have hinv : (⟨h, hh⟩ : H ⊤)⁻¹.1 p = p := by
    show h.symm p = p
    conv_lhs => rw [← hp]
    exact h.symm_apply_apply p
  refine ⟨⟨hTT ⟨h, hh⟩ hp, hTT (⟨h, hh⟩ : H ⊤)⁻¹ hinv⟩, ?_⟩
  obtain ⟨B, -, hloc⟩ := mem_H_top_pw hh
  have := hs.1
  obtain ⟨k, hk⟩ := germ_side (Finset.finite_toSet B) (locMob_of_isPiecewiseProjOn hloc) hs
  have hkp : mob k p = p := by rw [← eq_mob_of_germ h.continuous hsp hk, hp]
  exact ⟨k, mem_Q1_of_mob_eq k hkp, Filter.eventually_map.2 hk⟩

end Monod.Dev.Alg

end
end

section
section
section
open scoped Pointwise Topology
open OnePoint
namespace ThompsonAmenability.JM
/-!
# Blueprint: JMMS Theorem 6.4 from the germ-groupoid theorem

JMMS (arXiv:1503.04977) p. 23: "Apply Theorem 6.5 to G = H1 with H the groupoid of germs of the
partial action of PSL(2, R) on the real line." We work on `P¹ = OnePoint ℝ` itself: `𝓗` is the
pseudogroup of partial homeomorphisms of `P¹` that are locally Möbius and send `∞` to `∞` and
finite points to finite points. Its full group is the affine group (metabelian), the germ groups
of subgroups of `H` are metabelian (left and right germs at a fixed point are Möbius maps fixing
it), elements of `H` are locally Möbius off finitely many breakpoints, and extensive amenability
on `ℝ` extends to `P¹` because `∞` is fixed.
-/
/-- `f` is locally Möbius on `u`, sending `∞` to `∞` and finite points to finite points. -/
def MobProp (f : OnePoint ℝ → OnePoint ℝ) (u : Set (OnePoint ℝ)) : Prop :=
  ∀ x ∈ u, ∃ g : Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ),
    (∀ᶠ y in 𝓝 x, f y = Monod.mob g y) ∧ (x = ∞ ↔ f x = ∞)

end ThompsonAmenability.JM
end

section
open scoped Pointwise Topology
open OnePoint Filter
namespace ThompsonAmenability.JM.PartP
open ThompsonAmenability.JM
/-!
# Part P: the Möbius pregroupoid axioms
-/
theorem mobProp_comp {f g : OnePoint ℝ → OnePoint ℝ} {u v : Set (OnePoint ℝ)}
    (hf : MobProp f u) (hg : MobProp g v) (_hu : IsOpen u) (_hv : IsOpen v)
    (_huv : IsOpen (u ∩ f ⁻¹' v)) : MobProp (g ∘ f) (u ∩ f ⁻¹' v) := by
  rintro x ⟨hxu, hxv⟩
  obtain ⟨a, ha, hax⟩ := hf x hxu
  obtain ⟨b, hb, hbx⟩ := hg (f x) hxv
  have hfx : f x = Monod.mob a x := ha.self_of_nhds
  have htend : Tendsto f (𝓝 x) (𝓝 (f x)) := by
    have h := (Monod.Dev.Alg.continuous_mob a).tendsto x
    rw [← hfx] at h
    exact h.congr' (ha.mono fun y hy => hy.symm)
  refine ⟨b * a, ?_, hax.trans hbx⟩
  filter_upwards [ha, htend.eventually hb] with y hy hgy
  rw [Function.comp_apply, Monod.Dev.Alg.mob_mul, hgy, hy]

end ThompsonAmenability.JM.PartP
end

section
open scoped Pointwise Topology
open OnePoint
namespace ThompsonAmenability.JM
/-! ## Part P: the Möbius pseudogroup -/
alias mobProp_comp := ThompsonAmenability.JM.PartP.mobProp_comp

end ThompsonAmenability.JM
end

section
open scoped Pointwise Topology
open OnePoint Filter
namespace ThompsonAmenability.JM.PartP
open ThompsonAmenability.JM
theorem mobProp_id : MobProp id Set.univ := by
  intro x _
  exact ⟨1, Eventually.of_forall fun y => (Monod.Dev.Alg.mob_one y).symm, Iff.rfl⟩

end ThompsonAmenability.JM.PartP
end

section
open scoped Pointwise Topology
open OnePoint
namespace ThompsonAmenability.JM
alias mobProp_id := ThompsonAmenability.JM.PartP.mobProp_id

end ThompsonAmenability.JM
end

section
open scoped Pointwise Topology
open OnePoint Filter
namespace ThompsonAmenability.JM.PartP
open ThompsonAmenability.JM
theorem mobProp_locality {f : OnePoint ℝ → OnePoint ℝ} {u : Set (OnePoint ℝ)} (_hu : IsOpen u)
    (h : ∀ x ∈ u, ∃ v, IsOpen v ∧ x ∈ v ∧ MobProp f (u ∩ v)) : MobProp f u := by
  intro x hx
  obtain ⟨v, -, hxv, hv⟩ := h x hx
  exact hv x ⟨hx, hxv⟩

end ThompsonAmenability.JM.PartP
end

section
open scoped Pointwise Topology
open OnePoint
namespace ThompsonAmenability.JM
alias mobProp_locality := ThompsonAmenability.JM.PartP.mobProp_locality

end ThompsonAmenability.JM
end

section
open scoped Pointwise Topology
open OnePoint Filter
namespace ThompsonAmenability.JM.PartP
open ThompsonAmenability.JM
theorem mobProp_congr {f g : OnePoint ℝ → OnePoint ℝ} {u : Set (OnePoint ℝ)} (hu : IsOpen u)
    (hfg : ∀ x ∈ u, g x = f x) (hf : MobProp f u) : MobProp g u := by
  intro x hx
  obtain ⟨a, ha, hax⟩ := hf x hx
  refine ⟨a, ?_, by rw [hfg x hx]; exact hax⟩
  filter_upwards [ha, hu.mem_nhds hx] with y hy hyu
  rw [hfg y hyu, hy]

end ThompsonAmenability.JM.PartP
end

section
open scoped Pointwise Topology
open OnePoint
namespace ThompsonAmenability.JM
alias mobProp_congr := ThompsonAmenability.JM.PartP.mobProp_congr

/-- The pregroupoid of locally Möbius maps preserving `{∞}`. -/
def mobPregroupoid : Pregroupoid (OnePoint ℝ) where
  property := MobProp
  comp := mobProp_comp
  id_mem := mobProp_id
  locality := mobProp_locality
  congr := mobProp_congr

/-- The pseudogroup `𝓗`. -/
def mobGroupoid : StructureGroupoid (OnePoint ℝ) := mobPregroupoid.groupoid

end ThompsonAmenability.JM
end

section
open scoped Pointwise Topology
open OnePoint Filter
namespace ThompsonAmenability.JM.PartQ
open Monod.Dev.Alg
/-!
# Part Q: the full group of the Möbius pseudogroup is amenable

Every element of `[[𝓗]]` is locally Möbius everywhere, so (`ℝ` being connected) a single Möbius
map on `ℝ`; it sends finite points to finite points, so it is affine, `x ↦ a x + b`. The slope is
a homomorphism to `ℝˣ` whose kernel (the translations) is abelian, so `[[𝓗]]` is solvable.
-/
/-- An element of the full group fixes `∞` and is affine on `ℝ`. -/
theorem affine_of_mem {f : OnePoint ℝ ≃ₜ OnePoint ℝ}
    (hf : f ∈ GermGroupoid.fullGroup mobGroupoid) :
    f ∞ = ∞ ∧ ∃ a b : ℝ, a ≠ 0 ∧ ∀ x : ℝ, f x = ((a * x + b : ℝ) : OnePoint ℝ) := by
  -- local data at each point
  have hloc : ∀ x, ∃ g : Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ),
      (∀ᶠ y in 𝓝 x, f y = Monod.mob g y) ∧ (x = ∞ ↔ f x = ∞) := by
    intro x
    obtain ⟨e, he, hxe, hfe⟩ := hf x
    obtain ⟨g, hg, hinf⟩ := (mem_groupoid_of_pregroupoid.mp he).1 x hxe
    have hfx : f x = e x := hfe.self_of_nhds
    refine ⟨g, ?_, ?_⟩
    · filter_upwards [hfe, hg] with y h1 h2
      rw [h1, h2]
    · rw [hfx]; exact hinf
  have hfinf : f ∞ = ∞ := by
    obtain ⟨_, _, h⟩ := hloc ∞
    exact h.mp rfl
  refine ⟨hfinf, ?_⟩
  have hL : LocMob (⊤ : Subring ℝ) ∅ f := fun x _ => by
    obtain ⟨g, hg, _⟩ := hloc x
    exact ⟨g, hg⟩
  obtain ⟨g, hg⟩ := germ_on_preconnected hL isOpen_univ isPreconnected_univ
    (fun _ _ => Set.notMem_empty _)
  have hfin : ∀ x : ℝ, f x ≠ ∞ := by
    intro x h
    obtain ⟨_, _, h'⟩ := hloc (x : OnePoint ℝ)
    exact OnePoint.coe_ne_infty x (h'.mpr h)
  have hc : ent g 1 0 = 0 := by
    by_contra hc
    have hx := hfin (-(ent g 1 1) / ent g 1 0)
    rw [hg _ (Set.mem_univ _), mob_coe, if_pos (by field_simp; ring)] at hx
    exact hx rfl
  have hdet := ent_det g
  rw [hc] at hdet
  have hd : ent g 1 1 ≠ 0 := by
    intro h; rw [h] at hdet; norm_num at hdet
  have ha : ent g 0 0 ≠ 0 := by
    intro h; rw [h] at hdet; norm_num at hdet
  refine ⟨ent g 0 0 / ent g 1 1, ent g 0 1 / ent g 1 1, div_ne_zero ha hd, fun x => ?_⟩
  rw [hg _ (Set.mem_univ _), mob_coe, hc, if_neg (by simpa using hd)]
  congr 1
  simp only [zero_mul, zero_add, div_eq_mul_inv]
  ring

/-- The real value of a point of `P¹` (`0` at `∞`). -/
noncomputable def val (p : OnePoint ℝ) : ℝ := p.elim 0 id

@[simp] lemma val_coe (x : ℝ) : val (x : OnePoint ℝ) = x := rfl

/-- The slope of a map, read off at `0` and `1`. -/
noncomputable def slope (f : OnePoint ℝ ≃ₜ OnePoint ℝ) : ℝ :=
  val (f ((1 : ℝ) : OnePoint ℝ)) - val (f ((0 : ℝ) : OnePoint ℝ))

lemma slope_eq {f : OnePoint ℝ ≃ₜ OnePoint ℝ} {a b : ℝ}
    (h : ∀ x : ℝ, f x = ((a * x + b : ℝ) : OnePoint ℝ)) : slope f = a := by
  simp only [slope, h, val_coe]; ring

/-- The slope homomorphism. -/
noncomputable def slopeHom : GermGroupoid.fullGroup mobGroupoid →* ℝˣ where
  toFun f := Units.mk0 (slope f) (by
    obtain ⟨_, a, b, ha, h⟩ := affine_of_mem f.2
    rw [slope_eq h]; exact ha)
  map_one' := by
    ext
    simp only [Units.val_mk0, Units.val_one]
    exact slope_eq (a := 1) (b := 0) (fun x => by simp)
  map_mul' f g := by
    ext
    simp only [Units.val_mk0, Units.val_mul]
    obtain ⟨_, a, b, _, hfa⟩ := affine_of_mem f.2
    obtain ⟨_, c, d, _, hgc⟩ := affine_of_mem g.2
    rw [slope_eq hfa, slope_eq hgc]
    refine slope_eq (b := a * d + b) (fun x => ?_)
    change (f : OnePoint ℝ ≃ₜ OnePoint ℝ) ((g : OnePoint ℝ ≃ₜ OnePoint ℝ) x) = _
    rw [hgc, hfa]; congr 1; ring

lemma comm_of_ker (f g : slopeHom.ker) : f * g = g * f := by
  have key : ∀ h : slopeHom.ker, (h : OnePoint ℝ ≃ₜ OnePoint ℝ) ∞ = ∞ ∧
      ∃ b : ℝ, ∀ x : ℝ, (h : OnePoint ℝ ≃ₜ OnePoint ℝ) x = ((x + b : ℝ) : OnePoint ℝ) := by
    intro h
    obtain ⟨hinf, a, b, _, ha⟩ := affine_of_mem (h : GermGroupoid.fullGroup mobGroupoid).2
    have h1 : slope (h : OnePoint ℝ ≃ₜ OnePoint ℝ) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.mp h.2)
      simpa [slopeHom] using this
    rw [slope_eq ha] at h1
    subst h1
    exact ⟨hinf, b, fun x => by rw [ha]; simp⟩
  obtain ⟨hfi, b, hf⟩ := key f
  obtain ⟨hgi, d, hg⟩ := key g
  apply Subtype.ext; apply Subtype.ext; apply Homeomorph.ext
  intro p
  change (f : OnePoint ℝ ≃ₜ OnePoint ℝ) ((g : OnePoint ℝ ≃ₜ OnePoint ℝ) p) =
    (g : OnePoint ℝ ≃ₜ OnePoint ℝ) ((f : OnePoint ℝ ≃ₜ OnePoint ℝ) p)
  induction p using OnePoint.rec with
  | infty => rw [hgi, hfi, hgi]
  | coe x => rw [hg, hf, hf, hg]; congr 1; ring

instance : Group.IsSolvable slopeHom.ker := Group.isSolvable_of_comm comm_of_ker

instance : Group.IsSolvable (GermGroupoid.fullGroup mobGroupoid) :=
  Group.isSolvable_of_ker_le_range slopeHom.ker.subtype slopeHom (by simp)

theorem isAmenable_fullGroup_mob : Garrido.IsAmenable (GermGroupoid.fullGroup mobGroupoid) :=
  Garrido.isAmenable_of_isSolvable_of_finiteIndex ⊤ inferInstance

end ThompsonAmenability.JM.PartQ
end

section
open scoped Pointwise Topology
open OnePoint
namespace ThompsonAmenability.JM
/-! ## Part Q: `[[𝓗]]` is amenable (it is the affine group) -/
alias isAmenable_fullGroup_mob := ThompsonAmenability.JM.PartQ.isAmenable_fullGroup_mob

end ThompsonAmenability.JM
end

section
open scoped Pointwise Topology
open OnePoint Filter
namespace ThompsonAmenability.JM.PartR
open ThompsonAmenability.JM
/-!
# Part R: elements of `H` have their germs in `𝓗` off finitely many points
-/
/-- A homeomorphism fixing `∞` that is locally Möbius on an open set `s` has its germs in `𝓗`
at the points of `s`. -/
theorem germMem_of_locMob {f : OnePoint ℝ ≃ₜ OnePoint ℝ} (hinf : f ∞ = ∞)
    {s : Set (OnePoint ℝ)} (hs : IsOpen s)
    (hloc : ∀ x ∈ s, ∃ g : Matrix.SpecialLinearGroup (Fin 2) (⊤ : Subring ℝ),
      ∀ᶠ y in 𝓝 x, f y = Monod.mob g y)
    {x : OnePoint ℝ} (hx : x ∈ s) : GermGroupoid.GermMem mobGroupoid f x := by
  have hiff : ∀ z, z = ∞ ↔ f z = ∞ := fun z => by
    constructor
    · rintro rfl; exact hinf
    · intro h; exact f.injective (h.trans hinf.symm)
  have hiff' : ∀ z, z = ∞ ↔ f.symm z = ∞ := fun z => by
    rw [hiff (f.symm z), Homeomorph.apply_symm_apply]
  let e := f.toOpenPartialHomeomorph.restrOpen s hs
  refine ⟨e, ?_, ?_, Eventually.of_forall fun y => rfl⟩
  · rw [mobGroupoid, mem_groupoid_of_pregroupoid]
    constructor
    · intro z hz
      have hzs : z ∈ s := by
        simpa [e, OpenPartialHomeomorph.restrOpen_source] using hz
      obtain ⟨g, hg⟩ := hloc z hzs
      exact ⟨g, hg, hiff z⟩
    · intro w hw
      have hws : f.symm w ∈ s := by
        have : w ∈ e.target := hw
        simpa [e, OpenPartialHomeomorph.restrOpen, OpenPartialHomeomorph.restr,
          OpenPartialHomeomorph.IsImage.restr] using this
      obtain ⟨g, hg⟩ := hloc _ hws
      refine ⟨g⁻¹, ?_, ?_⟩
      · have ht : Tendsto f.symm (𝓝 w) (𝓝 (f.symm w)) := f.symm.continuous.tendsto w
        filter_upwards [ht.eventually hg] with y hy
        change f.symm y = Monod.mob g⁻¹ y
        rw [Homeomorph.apply_symm_apply] at hy
        exact (Monod.Dev.Alg.mob_inv_mob g (f.symm y)).symm.trans (congrArg _ hy.symm)
      · exact hiff' w
  · simpa [e, OpenPartialHomeomorph.restrOpen_source] using hx

theorem finite_not_germMem {f : OnePoint ℝ ≃ₜ OnePoint ℝ} (hf : f ∈ Monod.Hpp) :
    {x | ¬ GermGroupoid.GermMem mobGroupoid f x}.Finite := by
  have hf' : f ∈ Monod.H ⊤ := Monod.Gpp_eq_G_top_and_Hpp_eq_H_top.2 ▸ hf
  obtain ⟨hG, hinf⟩ := Subgroup.mem_inf.mp hf'
  obtain ⟨-, B, -, hB⟩ := (Monod.mem_G_iff_isPiecewiseProj ⊤ f).mp hG
  have hopen : IsOpen ((↑B : Set (OnePoint ℝ))ᶜ) := B.finite_toSet.isClosed.isOpen_compl
  refine B.finite_toSet.subset fun x hx => ?_
  by_contra hxB
  exact hx (germMem_of_locMob hinf hopen (fun y hy => hB y hy) hxB)

end ThompsonAmenability.JM.PartR
end

section
open scoped Pointwise Topology
open OnePoint
namespace ThompsonAmenability.JM
/-! ## Part R: elements of `H` have their germs in `𝓗` off finitely many points -/
alias finite_not_germMem := ThompsonAmenability.JM.PartR.finite_not_germMem

end ThompsonAmenability.JM
end

section
open Filter Topology OnePoint
open Monod.Dev.Alg
namespace ThompsonAmenability.JM.PartS
/-!
# Part S: the germ groups of subgroups of `H` are amenable

The second derived subgroup of the stabilizer of `x` acts trivially near `x` (its left and right
germs at `x` are Möbius maps in the second derived subgroup of the stabilizer of the line `x`,
which acts trivially on `P¹`), so the germ group is solvable of length at most `2`.
-/
/-- A subgroup of `H ⊤` fixing `p`: its second derived subgroup acts trivially near `p`. -/
theorem eventually_id_of_mem_second_derived (Γ : Subgroup (OnePoint ℝ ≃ₜ OnePoint ℝ))
    (hΓ : Γ ≤ Monod.H ⊤) {p : OnePoint ℝ} (hp : ∀ u ∈ Γ, u p = p)
    {w : OnePoint ℝ ≃ₜ OnePoint ℝ} (hw : w ∈ ⁅⁅Γ, Γ⁆, ⁅Γ, Γ⁆⁆) :
    ∀ᶠ y in 𝓝 p, w y = y := by
  have side : ∀ s : Filter ℝ, GoodSide s → Filter.map ((↑) : ℝ → OnePoint ℝ) s ≤ 𝓝 p →
      (∀ u : Monod.H ⊤, (u : OnePoint ℝ ≃ₜ OnePoint ℝ) p = p → Tendsto (ψ u) s s) →
      ∀ᶠ x in Filter.map ((↑) : ℝ → OnePoint ℝ) s, w x = x := by
    intro s hs hsp htend
    set F := Filter.map ((↑) : ℝ → OnePoint ℝ) s
    have hΓ1 : Γ ≤ GS F (Q1 ⊤ (vec p) (vec_ne_zero p)) := fun u hu =>
      mem_GS_side (hΓ hu) (hp u hu) hs hsp htend
    have h1 : ⁅Γ, Γ⁆ ≤ GS F (Q2 ⊤ (vec p)) :=
      (Subgroup.commutator_mono hΓ1 hΓ1).trans ((commutator_GS_le F _).trans
        (GS_mono F (commutator_Q1_le _ _)))
    have h2 : ⁅⁅Γ, Γ⁆, ⁅Γ, Γ⁆⁆ ≤ GS F (Qid ⊤) :=
      (Subgroup.commutator_mono h1 h1).trans ((commutator_GS_le F _).trans
        (GS_mono F (commutator_Q2_le p)))
    obtain ⟨-, k, hk, e⟩ := h2 hw
    filter_upwards [e] with x hx
    rw [hx, hk x]
  have hc : ∀ H : Subgroup (OnePoint ℝ ≃ₜ OnePoint ℝ), ⁅H, H⁆ ≤ H := by
    intro H
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have hΓ'' : ⁅⁅Γ, Γ⁆, ⁅Γ, Γ⁆⁆ ≤ Γ := (hc _).trans (hc _)
  have hwp : w p = p := hp w (hΓ'' hw)
  have hL := side (sideL p) (goodSide_sideL p) (sideL_le p)
    (fun u hu => tendsto_sideL (ψ u) p (ψ_fix hu))
  have hR := side (sideR p) (goodSide_sideR p) (sideR_le p)
    (fun u hu => tendsto_sideR (ψ u) p (ψ_fix hu))
  apply Filter.Eventually.filter_mono (nhds_le_sides p)
  rw [Filter.eventually_sup, Filter.eventually_sup]
  exact ⟨⟨hL, hR⟩, Filter.eventually_pure.2 hwp⟩

theorem isAmenable_germGroup (K : Subgroup (OnePoint ℝ ≃ₜ OnePoint ℝ)) (hK : K ≤ Monod.Hpp)
    (x : OnePoint ℝ) : Garrido.IsAmenable (GermGroupoid.GermGroup K x) := by
  set S := MulAction.stabilizer K x
  set N := GermGroupoid.germKernel K x
  let φ : S →* (OnePoint ℝ ≃ₜ OnePoint ℝ) := K.subtype.comp (Subgroup.subtype S)
  set Γ := (⊤ : Subgroup S).map φ
  have hΓH : Γ ≤ Monod.H ⊤ := by
    rintro _ ⟨s, -, rfl⟩
    rw [← Monod.Gpp_eq_G_top_and_Hpp_eq_H_top.2]
    exact hK (s : K).2
  have hΓp : ∀ u ∈ Γ, u x = x := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  have hder : derivedSeries S 2 ≤ N := by
    intro w hw
    have hmap : φ w ∈ ⁅⁅Γ, Γ⁆, ⁅Γ, Γ⁆⁆ := by
      have : (derivedSeries S 2).map φ = ⁅⁅Γ, Γ⁆, ⁅Γ, Γ⁆⁆ := by
        simp only [derivedSeries_succ, derivedSeries_zero, Subgroup.map_commutator, Γ]
      rw [← this]
      exact ⟨w, hw, rfl⟩
    exact eventually_id_of_mem_second_derived Γ hΓH hΓp hmap
  have hsolv : Group.IsSolvable (GermGroupoid.GermGroup K x) := by
    refine ⟨⟨2, ?_⟩⟩
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective N)]
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hder
  have : Group.IsSolvable (⊤ : Subgroup (GermGroupoid.GermGroup K x)) :=
    Group.isSolvable_of_isSolvable_injective (f := (⊤ : Subgroup _).subtype) Subtype.val_injective
  exact Garrido.isAmenable_of_isSolvable_of_finiteIndex ⊤ this

end ThompsonAmenability.JM.PartS
end

section
open scoped Pointwise Topology
open OnePoint
namespace ThompsonAmenability.JM
/-! ## Part S: the germ groups of subgroups of `H` are amenable -/
alias isAmenable_germGroup := ThompsonAmenability.JM.PartS.isAmenable_germGroup

/-! ## The theorem -/
theorem chk_isAmenable_iff_isExtensivelyAmenableOn_of_le_Hpp
    (K : Subgroup (OnePoint ℝ ≃ₜ OnePoint ℝ)) (hK : K ≤ Monod.Hpp) :
    Garrido.IsAmenable K ↔
      IsExtensivelyAmenableOn K (OnePoint ℝ) (Set.range ((↑) : ℝ → OnePoint ℝ)) := by
  have hinf : ∀ k : K, k • (∞ : OnePoint ℝ) = ∞ := fun k => (Subgroup.mem_inf.mp (hK k.2)).2
  constructor
  · intro hA
    refine Dev.Chornyi.isExtensivelyAmenableOn_of_isAmenable _ ?_ hA
    rintro k x ⟨t, rfl⟩
    have hne : k • ((t : ℝ) : OnePoint ℝ) ≠ ∞ := by
      intro h
      have h' : k • ((t : ℝ) : OnePoint ℝ) = k • (∞ : OnePoint ℝ) := by rw [h, hinf k]
      exact OnePoint.coe_ne_infty t (smul_left_cancel k h')
    obtain ⟨s, hs⟩ := OnePoint.ne_infty_iff_exists.mp hne
    exact ⟨s, hs⟩
  · intro hE
    classical
    have hU : IsExtensivelyAmenableOn K (OnePoint ℝ) Set.univ := by
      have h := FAmenHZ.isExtensivelyAmenableOn_insert _ ∞ hinf hE
      have heq : insert ∞ (Set.range ((↑) : ℝ → OnePoint ℝ)) = Set.univ := by
        ext x
        induction x using OnePoint.rec with
        | infty => simp
        | coe t => simp
      rwa [heq] at h
    exact GermGroupoid.isAmenable_of_isExtensivelyAmenableOn K mobGroupoid
      (fun g hg => finite_not_germMem (hK hg)) (isAmenable_germGroup K hK) hU
      isAmenable_fullGroup_mob

end ThompsonAmenability.JM
end

end
end

section
section
namespace ThompsonAmenability

theorem isAmenable_iff_isExtensivelyAmenableOn_of_le_Hpp
    (K : Subgroup (OnePoint ℝ ≃ₜ OnePoint ℝ)) (hK : K ≤ Monod.Hpp) :
    Garrido.IsAmenable K ↔
      IsExtensivelyAmenableOn K (OnePoint ℝ) (Set.range ((↑) : ℝ → OnePoint ℝ)) :=
  JM.chk_isAmenable_iff_isExtensivelyAmenableOn_of_le_Hpp K hK

end ThompsonAmenability

end
end

section
open ThompsonAmenability

theorem solution
    (K : Subgroup (OnePoint ℝ ≃ₜ OnePoint ℝ)) (hK : K ≤ Monod.Hpp) :
    Garrido.IsAmenable K ↔
      IsExtensivelyAmenableOn K (OnePoint ℝ) (Set.range ((↑) : ℝ → OnePoint ℝ)) := by
  apply ThompsonAmenability.isAmenable_iff_isExtensivelyAmenableOn_of_le_Hpp <;> assumption

end
