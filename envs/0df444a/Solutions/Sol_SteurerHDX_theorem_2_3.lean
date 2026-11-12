-- Prove2me | solution 1 for SteurerHDX.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T00:50:04.153611+00:00
-- url     : https://prove2.me/submissions/cd375e1b-e41e-4b2d-8140-17750f2dc031

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_SteurerHDX_IsConnectedComplex
import Definitions.Def_SteurerHDX_IsTopLinkExpander
import Definitions.Def_SteurerHDX_spectralGap
import Definitions.Def_SteurerHDX_downUp
import Theorems.Thm_SteurerHDX_lemma_2_1

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace SteurerHDX.Dev.T23

variable {V : Type*} [DecidableEq V]

/-- number of facets (d-faces) containing `α` (the weight Π_j of Alev–Lau, up to scaling) -/
def fc (X : Finset (Finset V)) (d : ℕ) (α : Finset V) : ℕ :=
  ((faces X d).filter (fun σ => α ⊆ σ)).card

/-- weighted down-up walk on X(j), weights = facet counts (Alev–Lau's P^∨_j for Π induced
from the uniform measure on X(d)). -/
noncomputable def wDownUp (X : Finset (Finset V)) (d j : ℕ) : Matrix (faces X j) (faces X j) ℝ :=
  Matrix.of fun a b => (1 / (j : ℝ)) * ∑ v ∈ a.1,
    if a.1.erase v ⊆ b.1 then
      (fc X d b.1 : ℝ) / ∑ ρ ∈ (faces X j).filter (fun ρ => a.1.erase v ⊆ ρ), (fc X d ρ : ℝ)
    else 0

/-- weighted 1-skeleton adjacency of the link of `α` (edge {x,y} has weight fc(α ∪ x ∪ y)). -/
noncomputable def wLinkAdj (X : Finset (Finset V)) (d : ℕ) (α : Finset V) :
    Matrix (faces (link X α) 1) (faces (link X α) 1) ℝ :=
  Matrix.of fun x y => if x ≠ y ∧ x.1 ∪ y.1 ∈ link X α then (fc X d (α ∪ x.1 ∪ y.1) : ℝ) else 0

noncomputable def wLam (X : Finset (Finset V)) (d : ℕ) (α : Finset V) : ℝ :=
  lambdaTwo (wLinkAdj X d α)

section FcFacts
variable (X : Finset (Finset V)) (d : ℕ)

lemma mem_faces_iff (i : ℕ) (σ : Finset V) : σ ∈ faces X i ↔ σ ∈ X ∧ σ.card = i := by
  simp [faces]

lemma fc_ne_zero_mem (hX : IsPure X d) (γ : Finset V) (h : fc X d γ ≠ 0) : γ ∈ X := by
  unfold fc at h
  obtain ⟨σ, hσ⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero h)
  rw [Finset.mem_filter, mem_faces_iff] at hσ
  exact hX.1 σ hσ.1.1 γ hσ.2

lemma fc_mono (γ γ' : Finset V) (h : γ ⊆ γ') : fc X d γ' ≤ fc X d γ := by
  unfold fc
  apply Finset.card_le_card
  intro σ hσ
  rw [Finset.mem_filter] at hσ ⊢
  exact ⟨hσ.1, h.trans hσ.2⟩

lemma exists_facet (hX : IsPure X d) (γ : Finset V) (hγ : γ ∈ X) :
    ∃ σ ∈ faces X d, γ ⊆ σ := by
  obtain ⟨ρ, hρ, hmax⟩ := Finset.exists_maximal
    (⟨γ, Finset.mem_filter.2 ⟨hγ, subset_rfl⟩⟩ : (X.filter (fun ρ => γ ⊆ ρ)).Nonempty)
  rw [Finset.mem_filter] at hρ
  refine ⟨ρ, (mem_faces_iff X d ρ).2 ⟨hρ.1, hX.2 ρ hρ.1 ?_⟩, hρ.2⟩
  intro ρ' hρ' hsub
  exact Finset.Subset.antisymm (hmax (Finset.mem_filter.2 ⟨hρ', hρ.2.trans hsub⟩) hsub) hsub

lemma fc_pos (hX : IsPure X d) (γ : Finset V) (hγ : γ ∈ X) : 0 < fc X d γ := by
  obtain ⟨σ, hσ, hs⟩ := exists_facet X d hX γ hγ
  exact Finset.card_pos.2 ⟨σ, Finset.mem_filter.2 ⟨hσ, hs⟩⟩

lemma card_le_of_mem (hX : IsPure X d) (γ : Finset V) (hγ : γ ∈ X) : γ.card ≤ d := by
  obtain ⟨σ, hσ, hs⟩ := exists_facet X d hX γ hγ
  have := ((mem_faces_iff X d σ).1 hσ).2
  have := Finset.card_le_card hs
  omega

lemma sum_fc_ext (hX : IsPure X d) (U : Finset V) (hU : ∀ σ ∈ X, σ ⊆ U) (γ : Finset V) :
    ∑ x ∈ U.filter (fun x => x ∉ γ), (fc X d (insert x γ) : ℝ) =
      ((d : ℝ) - γ.card) * fc X d γ := by
  by_cases h0 : fc X d γ = 0
  · rw [h0]
    simp only [Nat.cast_zero, mul_zero]
    refine Finset.sum_eq_zero fun x _ => ?_
    have := fc_mono X d γ (insert x γ) (Finset.subset_insert _ _)
    have : fc X d (insert x γ) = 0 := by omega
    simp [this]
  · have hγ := fc_ne_zero_mem X d hX γ h0
    have hcd := card_le_of_mem X d hX γ hγ
    have key : ∑ x ∈ U.filter (fun x => x ∉ γ), fc X d (insert x γ) = (d - γ.card) * fc X d γ := by
      unfold fc
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
      have : ∀ σ ∈ faces X d, ∑ x ∈ U.filter (fun x => x ∉ γ), (if insert x γ ⊆ σ then 1 else 0) =
          if γ ⊆ σ then d - γ.card else 0 := by
        intro σ hσ
        obtain ⟨hσX, hσc⟩ := (mem_faces_iff X d σ).1 hσ
        by_cases hs : γ ⊆ σ
        · rw [if_pos hs]
          simp only [Finset.insert_subset_iff, hs, and_true]
          rw [← Finset.card_filter]
          have : (U.filter (fun x => x ∉ γ)).filter (fun x => x ∈ σ) = σ \ γ := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_sdiff]
            constructor
            · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
            · rintro ⟨h1, h2⟩; exact ⟨⟨hU σ hσX h1, h2⟩, h1⟩
          rw [this, Finset.card_sdiff_of_subset hs, hσc]
        · rw [if_neg hs]
          refine Finset.sum_eq_zero fun x _ => ?_
          rw [if_neg]
          intro h; exact hs ((Finset.subset_insert _ _).trans h)
      rw [Finset.sum_congr rfl this]
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
      rw [Finset.card_filter]
    have := congrArg (fun n : ℕ => (n : ℝ)) key
    simp only [Nat.cast_sum, Nat.cast_mul] at this
    rw [this, Nat.cast_sub hcd]

end FcFacts

section Weights
variable (X : Finset (Finset V)) (d : ℕ)

/-- all vertices occurring in faces of `X` -/
def Uv : Finset V := X.biUnion id

lemma subset_Uv (σ : Finset V) (hσ : σ ∈ X) : σ ⊆ Uv X :=
  fun x hx => Finset.mem_biUnion.2 ⟨σ, hσ, hx⟩

/-- vertex weight of the link of `γ` -/
noncomputable def cW (γ : Finset V) (y : V) : ℝ :=
  if y ∉ γ then (fc X d (insert y γ) : ℝ) else 0

/-- edge weight of the link of `γ` -/
noncomputable def wW (γ : Finset V) (y z : V) : ℝ :=
  if y ∉ γ ∧ z ∉ γ ∧ y ≠ z then (fc X d (insert y (insert z γ)) : ℝ) else 0

lemma fc_zero_of_not_mem (hX : IsPure X d) (γ : Finset V) (h : γ ∉ X) : fc X d γ = 0 := by
  by_contra h'
  exact h (fc_ne_zero_mem X d hX γ h')

lemma fc_zero_of_sub (hX : IsPure X d) (γ γ' : Finset V) (hs : γ ⊆ γ') (h : γ ∉ X) :
    fc X d γ' = 0 := by
  have := fc_mono X d γ γ' hs
  have := fc_zero_of_not_mem X d hX γ h
  omega

lemma cW_nonneg (γ : Finset V) (y : V) : 0 ≤ cW X d γ y := by
  unfold cW; split_ifs <;> positivity

lemma wW_nonneg (γ : Finset V) (y z : V) : 0 ≤ wW X d γ y z := by
  unfold wW; split_ifs <;> positivity

lemma wW_comm (γ : Finset V) (y z : V) : wW X d γ y z = wW X d γ z y := by
  unfold wW
  by_cases h : y ∉ γ ∧ z ∉ γ ∧ y ≠ z
  · rw [if_pos h, if_pos ⟨h.2.1, h.1, h.2.2.symm⟩, Finset.insert_comm]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2.1, h'.1, h'.2.2.symm⟩)]

lemma cW_insert (γ : Finset V) (x y : V) (hx : x ∉ γ) :
    cW X d (insert x γ) y = wW X d γ x y := by
  unfold cW wW
  by_cases hy : y ∉ γ ∧ y ≠ x
  · have h1 : y ∉ insert x γ := by simp [hy.1, hy.2]
    rw [if_pos h1, if_pos ⟨hx, hy.1, hy.2.symm⟩, Finset.insert_comm]
  · have h1 : ¬ y ∉ insert x γ := by simp only [Finset.mem_insert]; tauto
    rw [if_neg h1, if_neg]
    rintro ⟨_, h2, h3⟩
    exact hy ⟨h2, h3.symm⟩

lemma cW_zero_of_not_mem (hX : IsPure X d) (γ : Finset V) (y : V) (h : insert y γ ∉ X) :
    cW X d γ y = 0 := by
  unfold cW
  by_cases hy : y ∈ γ
  · simp [hy]
  · rw [if_pos hy, fc_zero_of_not_mem X d hX _ h]; simp

lemma wW_zero_of_not_mem (hX : IsPure X d) (γ : Finset V) (x y : V) (h : insert y γ ∉ X) :
    wW X d γ x y = 0 := by
  unfold wW
  split_ifs with hc
  · have : fc X d (insert x (insert y γ)) = 0 :=
      fc_zero_of_sub X d hX _ _ (Finset.subset_insert _ _) h
    simp [this]
  · rfl

lemma sum_wW (hX : IsPure X d) (γ : Finset V) (y : V) :
    ∑ z ∈ Uv X, wW X d γ y z = ((d : ℝ) - γ.card - 1) * cW X d γ y := by
  by_cases hy : y ∈ γ
  · simp [wW, cW, hy]
  · have h := sum_fc_ext X d hX (Uv X) (subset_Uv X) (insert y γ)
    rw [Finset.sum_filter, Finset.card_insert_of_notMem hy] at h
    rw [cW, if_pos hy]
    have e : ∀ z ∈ Uv X, wW X d γ y z =
        if z ∉ insert y γ then (fc X d (insert z (insert y γ)) : ℝ) else 0 := by
      intro z _
      unfold wW
      by_cases hz : z ∉ insert y γ
      · rw [if_pos hz]
        have hz' : z ≠ y ∧ z ∉ γ := by simpa using hz
        rw [if_pos ⟨hy, hz'.2, hz'.1.symm⟩, Finset.insert_comm]
      · rw [if_neg hz, if_neg]
        rintro ⟨_, h2, h3⟩
        exact hz (by simp [h2, h3.symm])
    rw [Finset.sum_congr rfl e, h]
    push_cast
    ring

lemma sum_wW_ext (hX : IsPure X d) (α : Finset V) (y z : V) :
    ∑ x ∈ (Uv X).filter (fun x => x ∉ α), wW X d (insert x α) y z =
      ((d : ℝ) - α.card - 2) * wW X d α y z := by
  by_cases h : y ∉ α ∧ z ∉ α ∧ y ≠ z
  · have h2 := sum_fc_ext X d hX (Uv X) (subset_Uv X) (insert y (insert z α))
    have hzα : z ∉ α := h.2.1
    have hyz : y ∉ insert z α := by simp [h.1, h.2.2]
    rw [Finset.sum_filter, Finset.card_insert_of_notMem hyz,
      Finset.card_insert_of_notMem hzα] at h2
    rw [Finset.sum_filter]
    have e : ∀ x ∈ Uv X, (if x ∉ α then wW X d (insert x α) y z else 0) =
        if x ∉ insert y (insert z α) then
          (fc X d (insert x (insert y (insert z α))) : ℝ) else 0 := by
      intro x _
      by_cases hx : x ∉ insert y (insert z α)
      · have hx' : x ≠ y ∧ x ≠ z ∧ x ∉ α := by simpa using hx
        rw [if_pos hx, if_pos hx'.2.2]
        unfold wW
        rw [if_pos ⟨by simp [h.1, hx'.1.symm], by simp [h.2.1, hx'.2.1.symm], h.2.2⟩]
        congr 1
        congr 1
        ext t; simp only [Finset.mem_insert]; tauto
      · rw [if_neg hx]
        by_cases hxα : x ∉ α
        · rw [if_pos hxα]
          unfold wW
          rw [if_neg]
          rintro ⟨h1, h2', _⟩
          apply hx
          simp only [Finset.mem_insert, not_or] at h1 h2' ⊢
          exact ⟨fun e => h1.1 e.symm, fun e => h2'.1 e.symm, hxα⟩ 
        · rw [if_neg hxα]
    rw [Finset.sum_congr rfl e, h2]
    unfold wW
    rw [if_pos h]
    push_cast
    ring
  · have : ∀ x ∈ (Uv X).filter (fun x => x ∉ α), wW X d (insert x α) y z = 0 := by
      intro x _
      unfold wW
      rw [if_neg]
      rintro ⟨h1, h2, h3⟩
      exact h ⟨fun e => h1 (Finset.mem_insert_of_mem e), fun e => h2 (Finset.mem_insert_of_mem e), h3⟩
    rw [Finset.sum_eq_zero this]
    unfold wW
    rw [if_neg h]
    simp

end Weights

section LinkDict
variable (X : Finset (Finset V)) (d : ℕ)

lemma mem_iota (β : Finset V) (s : Finset V) :
    s ∈ faces (link X β) 1 ↔ ∃ x, s = {x} ∧ x ∉ β ∧ insert x β ∈ X := by
  unfold faces link
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨σ, ⟨hσX, hβσ⟩, hσs⟩, hc⟩
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 hc
    have hx : x ∈ σ \ β := by rw [hσs]; simp
    rw [Finset.mem_sdiff] at hx
    have : insert x β = σ := by
      apply Finset.Subset.antisymm
      · exact Finset.insert_subset hx.1 hβσ
      · intro t ht
        by_cases htb : t ∈ β
        · exact Finset.mem_insert_of_mem htb
        · have h3 : t ∈ σ \ β := Finset.mem_sdiff.2 ⟨ht, htb⟩
          rw [hσs] at h3
          simp only [Finset.mem_singleton] at h3
          simp [h3]
    exact ⟨x, rfl, hx.2, this ▸ hσX⟩
  · rintro ⟨x, rfl, hx, hX'⟩
    refine ⟨⟨insert x β, ⟨hX', Finset.subset_insert _ _⟩, ?_⟩, Finset.card_singleton x⟩
    ext t
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h | h, h2⟩
      · exact h
      · exact absurd h h2
    · rintro rfl
      exact ⟨Or.inl rfl, hx⟩

lemma union_mem_link (β a : Finset V) (h : a ∈ link X β) : β ∪ a ∈ X := by
  unfold link at h
  rw [Finset.mem_image] at h
  obtain ⟨σ, hσ, rfl⟩ := h
  rw [Finset.mem_filter] at hσ
  rw [Finset.union_sdiff_of_subset hσ.2]
  exact hσ.1

lemma sum_iota2 (β : Finset V) (G : Finset V → ℝ) (G' : V → ℝ)
    (h1 : ∀ x ∈ Uv X, x ∉ β → insert x β ∈ X → G {x} = G' x)
    (h2 : ∀ x ∈ Uv X, (x ∈ β ∨ insert x β ∉ X) → G' x = 0) :
    ∑ s : faces (link X β) 1, G s.1 = ∑ x ∈ Uv X, G' x := by
  rw [Finset.sum_coe_sort (faces (link X β) 1) G]
  have : faces (link X β) 1 =
      ((Uv X).filter (fun x => x ∉ β ∧ insert x β ∈ X)).image (fun x => ({x} : Finset V)) := by
    ext s
    rw [mem_iota, Finset.mem_image]
    constructor
    · rintro ⟨x, rfl, hx, hX'⟩
      exact ⟨x, Finset.mem_filter.2 ⟨subset_Uv X _ hX' (Finset.mem_insert_self _ _), hx, hX'⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      rw [Finset.mem_filter] at hx
      exact ⟨x, rfl, hx.2.1, hx.2.2⟩
  rw [this, Finset.sum_image (fun a _ b _ h => Finset.singleton_injective h), Finset.sum_filter]
  refine Finset.sum_congr rfl fun x hx => ?_
  by_cases hP : x ∉ β ∧ insert x β ∈ X
  · rw [if_pos hP, h1 x hx hP.1 hP.2]
  · rw [if_neg hP, h2 x hx]
    by_cases h : x ∈ β
    · exact Or.inl h
    · right; intro h'; exact hP ⟨h, h'⟩

lemma Phi_eq (hX : IsPure X d) (β : Finset V) (x y : V) (hx : x ∉ β) (hy : y ∉ β) :
    (if ({x} : Finset V) ≠ {y} ∧ {x} ∪ {y} ∈ link X β then (fc X d (β ∪ {x} ∪ {y}) : ℝ) else 0)
      = wW X d β x y := by
  unfold wW
  by_cases hxy : x = y
  · subst hxy; simp
  · have hset : β ∪ {x} ∪ {y} = insert x (insert y β) := by
      ext t; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto
    rw [if_pos (show x ∉ β ∧ y ∉ β ∧ x ≠ y from ⟨hx, hy, hxy⟩), hset]
    have hne : ({x} : Finset V) ≠ {y} := by simpa using hxy
    by_cases hl : {x} ∪ {y} ∈ link X β
    · rw [if_pos (show ({x} : Finset V) ≠ {y} ∧ {x} ∪ {y} ∈ link X β from ⟨hne, hl⟩)]
    · rw [if_neg (fun h => hl h.2)]
      have : insert x (insert y β) ∉ X := by
        intro hm
        apply hl
        unfold link
        rw [Finset.mem_image]
        refine ⟨insert x (insert y β), Finset.mem_filter.2 ⟨hm, ?_⟩, ?_⟩
        · intro t ht; simp [ht]
        · ext t
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
          constructor
          · rintro ⟨h1 | h1 | h1, h2⟩
            · exact Or.inl h1
            · exact Or.inr h1
            · exact absurd h1 h2
          · rintro (rfl | rfl)
            · exact ⟨Or.inl rfl, hx⟩
            · exact ⟨Or.inr (Or.inl rfl), hy⟩
      simp [fc_zero_of_not_mem X d hX _ this]

end LinkDict

namespace Spec
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option linter.unusedSectionVars false

lemma dot_mulVec_comm (S : Matrix ι ι ℝ) (hS : ∀ x y, S x y = S y x) (v w : ι → ℝ) :
    v ⬝ᵥ S *ᵥ w = (S *ᵥ v) ⬝ᵥ w := by
  have h : Sᵀ = S := by ext x y; exact hS y x
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h]

/-- Abstract second-eigenvalue Rayleigh bound. -/
lemma abstract_min_max (S : Matrix ι ι ℝ) (hS : ∀ x y, S x y = S y x)
    (b : ι → ι → ℝ) (lam : ι → ℝ)
    (horth : ∀ i j, b i ⬝ᵥ b j = if i = j then 1 else 0)
    (heig : ∀ j, S *ᵥ b j = lam j • b j)
    (hexp : ∀ g, g = ∑ j, (b j ⬝ᵥ g) • b j)
    (p q : ι) (hpq : p ≠ q) (hp : ∀ j, lam j ≤ lam p) (hq : ∀ j, j ≠ p → lam j ≤ lam q)
    (hle : ∀ g, g ⬝ᵥ S *ᵥ g ≤ g ⬝ᵥ g)
    (u : ι → ℝ) (hu0 : u ≠ 0) (hu : S *ᵥ u = u) :
    (∀ g, u ⬝ᵥ g = 0 → g ⬝ᵥ S *ᵥ g ≤ lam q * (g ⬝ᵥ g)) ∧
    (∃ g, g ≠ 0 ∧ u ⬝ᵥ g = 0 ∧ S *ᵥ g = lam q • g) := by
  have hdg : ∀ g, g ⬝ᵥ g = ∑ j, (b j ⬝ᵥ g) ^ 2 := by
    intro g
    calc g ⬝ᵥ g = g ⬝ᵥ ∑ j, (b j ⬝ᵥ g) • b j := by rw [← hexp g]
      _ = ∑ j, (b j ⬝ᵥ g) ^ 2 := by
        rw [dotProduct_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [dotProduct_smul, dotProduct_comm g (b j), smul_eq_mul, sq]
  have hdS : ∀ g, g ⬝ᵥ S *ᵥ g = ∑ j, lam j * (b j ⬝ᵥ g) ^ 2 := by
    intro g
    have h1 : S *ᵥ g = ∑ j, ((b j ⬝ᵥ g) * lam j) • b j := by
      conv_lhs => rw [hexp g]
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mulVec_smul, heig, smul_smul]
    rw [h1, dotProduct_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dotProduct_smul, dotProduct_comm g (b j), smul_eq_mul]; ring
  have hnorm : ∀ j, b j ⬝ᵥ b j = 1 := fun j => by simp [horth]
  have hlamp : lam p ≤ 1 := by
    have := hle (b p)
    rw [heig, dotProduct_smul, hnorm, smul_eq_mul] at this
    linarith
  -- u components
  have hucomp : ∀ j, lam j * (b j ⬝ᵥ u) = b j ⬝ᵥ u := by
    intro j
    have := dot_mulVec_comm S hS (b j) u
    rw [hu, heig, smul_dotProduct, smul_eq_mul] at this
    exact this.symm
  have hlamp1 : lam p = 1 ∨ lam q = lam p := by
    by_cases h : lam q = lam p
    · exact Or.inr h
    · left
      -- some component of u is nonzero
      by_contra hne
      have hall : ∀ j, b j ⬝ᵥ u = 0 := by
        intro j
        have := hucomp j
        have hj : lam j ≠ 1 := by
          intro h1
          have hjp : j = p ∨ lam j ≤ lam q := by
            by_cases hjp : j = p
            · exact Or.inl hjp
            · exact Or.inr (hq j hjp)
          rcases hjp with rfl | hjq
          · exact hne h1
          · have := hp q
            have := hlamp
            have hqp : lam q < lam p := lt_of_le_of_ne (hp q) h
            linarith
        have : (lam j - 1) * (b j ⬝ᵥ u) = 0 := by linarith
        rcases mul_eq_zero.mp this with h0 | h0
        · exact absurd (by linarith) hj
        · exact h0
      apply hu0
      rw [hexp u]
      simp [hall]
  have hcase : lam q = lam p ∨ (lam p = 1 ∧ lam q < 1 ∧ (∀ j, j ≠ p → b j ⬝ᵥ u = 0) ∧ b p ⬝ᵥ u ≠ 0) := by
    by_cases h : lam q = lam p
    · exact Or.inl h
    · right
      have h1 : lam p = 1 := hlamp1.resolve_right h
      have hqp : lam q < lam p := lt_of_le_of_ne (hp q) h
      have hz : ∀ j, j ≠ p → b j ⬝ᵥ u = 0 := by
        intro j hj
        have h2 := hucomp j
        have h3 := hq j hj
        have : (lam j - 1) * (b j ⬝ᵥ u) = 0 := by linarith
        rcases mul_eq_zero.mp this with h0 | h0
        · exfalso; linarith
        · exact h0
      refine ⟨h1, by linarith, hz, ?_⟩
      intro h0
      apply hu0
      rw [hexp u]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : j = p
      · subst hj; simp [h0]
      · simp [hz j hj]
  refine ⟨?_, ?_⟩
  · intro g hg
    rw [hdS, hdg, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : j = p
    · subst hj
      rcases hcase with h | ⟨h1, h2, hz, hne⟩
      · rw [h]
      · have : b j ⬝ᵥ g = 0 := by
          have h4 : u ⬝ᵥ g = (b j ⬝ᵥ u) * (b j ⬝ᵥ g) := by
            conv_lhs => rw [hexp u]
            rw [sum_dotProduct, Finset.sum_eq_single j]
            · rw [smul_dotProduct, smul_eq_mul]
            · intro i _ hi; rw [smul_dotProduct, hz i hi]; simp
            · simp
          rw [hg] at h4
          rcases mul_eq_zero.mp h4.symm with h | h
          · exact absurd h hne
          · exact h
        rw [this]; simp
    · exact mul_le_mul_of_nonneg_right (hq j hj) (sq_nonneg _)
  · rcases hcase with h | ⟨h1, h2, hz, hne⟩
    · by_cases hab : b p ⬝ᵥ u = 0 ∧ b q ⬝ᵥ u = 0
      · refine ⟨b p, ?_, ?_, ?_⟩
        · intro h0; have := hnorm p; rw [h0] at this; simp at this
        · rw [dotProduct_comm]; exact hab.1
        · rw [heig, h]
      · refine ⟨(b q ⬝ᵥ u) • b p - (b p ⬝ᵥ u) • b q, ?_, ?_, ?_⟩
        · intro h0
          apply hab
          have e1 : b p ⬝ᵥ ((b q ⬝ᵥ u) • b p - (b p ⬝ᵥ u) • b q) = b q ⬝ᵥ u := by
            rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, hnorm, horth p q, if_neg hpq]; simp
          have e2 : b q ⬝ᵥ ((b q ⬝ᵥ u) • b p - (b p ⬝ᵥ u) • b q) = -(b p ⬝ᵥ u) := by
            rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, hnorm, horth q p, if_neg hpq.symm]; simp
          rw [h0] at e1 e2
          simp at e1 e2
          exact ⟨by linarith, e1.symm⟩
        · rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_comm u (b p),
            dotProduct_comm u (b q)]
          simp only [smul_eq_mul]; ring
        · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, heig, heig, smul_sub,
            smul_smul, smul_smul, smul_smul, smul_smul, ← h]
          congr 1 <;> congr 1 <;> ring
    · refine ⟨b q, ?_, ?_, heig q⟩
      · intro h0; have := hnorm q; rw [h0] at this; simp at this
      · rw [dotProduct_comm]; exact hz q (Ne.symm hpq)

lemma second_eig (S : Matrix ι ι ℝ) (hS : ∀ x y, S x y = S y x) (hH : S.IsHermitian)
    (hcard : 2 ≤ Fintype.card ι)
    (hle : ∀ g, g ⬝ᵥ S *ᵥ g ≤ g ⬝ᵥ g)
    (u : ι → ℝ) (hu0 : u ≠ 0) (hu : S *ᵥ u = u) :
    (∀ g, u ⬝ᵥ g = 0 → g ⬝ᵥ S *ᵥ g ≤ hH.eigenvalues₀ ⟨1, hcard⟩ * (g ⬝ᵥ g)) ∧
    (∃ g, g ≠ 0 ∧ u ⬝ᵥ g = 0 ∧ S *ᵥ g = hH.eigenvalues₀ ⟨1, hcard⟩ • g) := by
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) with he
  have hidx : ∀ k : Fin (Fintype.card ι), hH.eigenvalues (e k) = hH.eigenvalues₀ k := by
    intro k
    show hH.eigenvalues₀ (e.symm (e k)) = _
    rw [Equiv.symm_apply_apply]
  have h0 : 0 < Fintype.card ι := by omega
  have := abstract_min_max S hS (fun j => ⇑(hH.eigenvectorBasis j)) hH.eigenvalues
    (by
      intro i j
      have := (orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal) i j
      rw [EuclideanSpace.inner_eq_star_dotProduct] at this
      simpa [dotProduct_comm] using this)
    (fun j => hH.mulVec_eigenvectorBasis j)
    (by
      intro g
      have := hH.eigenvectorBasis.sum_repr' (WithLp.toLp 2 g)
      have h2 := congrArg (fun x : EuclideanSpace ℝ ι => (x : ι → ℝ)) this
      simp only at h2
      convert h2.symm using 1
      ext k
      simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm])
    (e ⟨0, h0⟩) (e ⟨1, hcard⟩)
    (by intro h; have := e.injective h; simp [Fin.ext_iff] at this)
    (by
      intro j
      have h1 : hH.eigenvalues j = hH.eigenvalues₀ (e.symm j) := rfl
      rw [h1, hidx]
      exact hH.eigenvalues₀_antitone (Fin.le_def.mpr (Nat.zero_le _)))
    (by
      intro j hj
      have h1 : hH.eigenvalues j = hH.eigenvalues₀ (e.symm j) := rfl
      rw [h1, hidx]
      refine hH.eigenvalues₀_antitone (Fin.le_def.mpr ?_)
      have : e.symm j ≠ ⟨0, h0⟩ := by
        intro h; apply hj; rw [← h]; simp
      have : (e.symm j).val ≠ 0 := fun h => this (Fin.ext h)
      show 1 ≤ (e.symm j).val
      omega)
    hle u hu0 hu
  rwa [hidx] at this

section concrete
variable (W : Matrix ι ι ℝ) (hdeg : ∀ x, 0 < SteurerHDX.vdeg W x)
include hdeg

lemma sqrt_pos' (x : ι) : 0 < Real.sqrt (SteurerHDX.vdeg W x) := Real.sqrt_pos.mpr (hdeg x)

lemma sym_u : SteurerHDX.symWalk W *ᵥ (fun x => Real.sqrt (SteurerHDX.vdeg W x)) =
    fun x => Real.sqrt (SteurerHDX.vdeg W x) := by
  funext x
  have hx := sqrt_pos' W hdeg x
  simp only [Matrix.mulVec, dotProduct, SteurerHDX.symWalk, Matrix.of_apply]
  have : ∀ y, W x y / (Real.sqrt (SteurerHDX.vdeg W x) * Real.sqrt (SteurerHDX.vdeg W y)) *
      Real.sqrt (SteurerHDX.vdeg W y) = W x y / Real.sqrt (SteurerHDX.vdeg W x) := by
    intro y
    have hy := sqrt_pos' W hdeg y
    field_simp
  simp only [this, ← Finset.sum_div]
  show SteurerHDX.vdeg W x / _ = _
  exact Real.div_sqrt

lemma quad_form (f : ι → ℝ) :
    (fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x) ⬝ᵥ
      SteurerHDX.symWalk W *ᵥ (fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x) =
    ∑ x, ∑ y, W x y * f x * f y := by
  simp only [Matrix.mulVec, dotProduct, SteurerHDX.symWalk, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have hx := sqrt_pos' W hdeg x
  have hy := sqrt_pos' W hdeg y
  field_simp

lemma norm_form (f : ι → ℝ) :
    (fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x) ⬝ᵥ
      (fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x) = ∑ x, SteurerHDX.vdeg W x * f x ^ 2 := by
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun x _ => ?_
  have := Real.mul_self_sqrt (hdeg x).le
  calc _ = (Real.sqrt (SteurerHDX.vdeg W x) * Real.sqrt (SteurerHDX.vdeg W x)) * f x ^ 2 := by ring
    _ = _ := by rw [this]


lemma u_dot (f : ι → ℝ) :
    (fun x => Real.sqrt (SteurerHDX.vdeg W x)) ⬝ᵥ (fun x => Real.sqrt (SteurerHDX.vdeg W x) * f x) =
      ∑ x, SteurerHDX.vdeg W x * f x * 1 := by
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun x _ => ?_
  have := Real.mul_self_sqrt (hdeg x).le
  calc _ = (Real.sqrt (SteurerHDX.vdeg W x) * Real.sqrt (SteurerHDX.vdeg W x)) * f x * 1 := by ring
    _ = _ := by rw [this]
end concrete
end Spec

namespace Spec
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma quad_le (W : Matrix ι ι ℝ) (hsymm : ∀ x y, W x y = W y x) (hnn : ∀ x y, 0 ≤ W x y)
    (f : ι → ℝ) :
    ∑ x, ∑ y, W x y * f x * f y ≤ ∑ x, SteurerHDX.vdeg W x * f x ^ 2 := by
  have h2 : ∑ x, ∑ y, W x y * f x ^ 2 = ∑ x, SteurerHDX.vdeg W x * f x ^ 2 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_mul]; rfl
  have h3 : ∑ x, ∑ y, W x y * f y ^ 2 = ∑ x, SteurerHDX.vdeg W x * f x ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_mul]
    unfold SteurerHDX.vdeg
    congr 1
    exact Finset.sum_congr rfl fun y _ => hsymm _ _
  have h4 : 0 ≤ ∑ x, ∑ y, W x y * (f x - f y) ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => mul_nonneg (hnn x y) (sq_nonneg _)
  have h5 : ∑ x, ∑ y, W x y * (f x - f y) ^ 2 =
      (∑ x, ∑ y, W x y * f x ^ 2) + (∑ x, ∑ y, W x y * f y ^ 2) -
        2 * ∑ x, ∑ y, W x y * f x * f y := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  linarith

lemma spec_basic (W : Matrix ι ι ℝ) (hsymm : ∀ x y, W x y = W y x) (hnn : ∀ x y, 0 ≤ W x y)
    (hdeg : ∀ x, 0 < SteurerHDX.vdeg W x) (hcard : 2 ≤ Fintype.card ι) :
    (∀ h : ι → ℝ, ∑ x, SteurerHDX.vdeg W x * h x = 0 →
      ∑ x, ∑ y, W x y * h x * h y ≤
        SteurerHDX.lambdaTwo W * ∑ x, SteurerHDX.vdeg W x * h x ^ 2) ∧
    ∃ f : ι → ℝ, f ≠ 0 ∧ ∑ x, SteurerHDX.vdeg W x * f x = 0 ∧
      ∀ x, ∑ y, W x y * f y = SteurerHDX.lambdaTwo W * SteurerHDX.vdeg W x * f x := by
  set S := SteurerHDX.symWalk W with hSdef
  have hSsym : ∀ x y, S x y = S y x := by
    intro x y; simp only [hSdef, SteurerHDX.symWalk, Matrix.of_apply]
    rw [hsymm x y, mul_comm]
  have hH : S.IsHermitian := Matrix.IsHermitian.ext fun i j => by simpa using hSsym j i
  have hlam : SteurerHDX.lambdaTwo W = hH.eigenvalues₀ ⟨1, hcard⟩ := by
    unfold SteurerHDX.lambdaTwo
    rw [dif_pos ⟨hH, hcard⟩]
    rfl
  have hgOf : ∀ g : ι → ℝ, (fun x => Real.sqrt (SteurerHDX.vdeg W x) *
      (g x / Real.sqrt (SteurerHDX.vdeg W x))) = g := by
    intro g; funext x
    have := (sqrt_pos' W hdeg x).ne'
    field_simp
  have hle : ∀ g, g ⬝ᵥ S *ᵥ g ≤ g ⬝ᵥ g := by
    intro g
    have h := hgOf g
    set f : ι → ℝ := fun x => g x / Real.sqrt (SteurerHDX.vdeg W x)
    rw [← h, quad_form W hdeg, norm_form W hdeg]
    exact quad_le W hsymm hnn f
  have hx0 : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨x0⟩ := hx0
  have hu0 : (fun x => Real.sqrt (SteurerHDX.vdeg W x)) ≠ 0 := by
    intro h; have := congrFun h x0; exact (sqrt_pos' W hdeg x0).ne' this
  obtain ⟨hA, g0, hg0, hug0, hSg0⟩ := second_eig S hSsym hH hcard hle _ hu0 (sym_u W hdeg)
  rw [hlam]
  generalize hH.eigenvalues₀ ⟨1, hcard⟩ = ev at hA hSg0 ⊢
  refine ⟨?_, ?_⟩
  · intro h hh
    have hu : (fun x => Real.sqrt (SteurerHDX.vdeg W x)) ⬝ᵥ
        (fun x => Real.sqrt (SteurerHDX.vdeg W x) * h x) = 0 := by
      rw [u_dot W hdeg]
      simpa using hh
    have := hA _ hu
    rw [quad_form W hdeg, norm_form W hdeg] at this
    exact this
  · refine ⟨fun x => g0 x / Real.sqrt (SteurerHDX.vdeg W x), ?_, ?_, ?_⟩
    · intro h
      apply hg0
      funext x
      have h1 := congrFun h x
      have h2 := (sqrt_pos' W hdeg x).ne'
      simp only [Pi.zero_apply, div_eq_zero_iff] at h1
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 h2
    · have hu : ∑ x, Real.sqrt (SteurerHDX.vdeg W x) * g0 x = 0 := hug0
      rw [← hu]
      refine Finset.sum_congr rfl fun x _ => ?_
      have h2 := Real.mul_self_sqrt (hdeg x).le
      have h3 := (sqrt_pos' W hdeg x).ne'
      field_simp
      rw [Real.sq_sqrt (hdeg x).le]; ring
    · intro x
      have hx := congrFun hSg0 x
      simp only [Matrix.mulVec, dotProduct, hSdef, SteurerHDX.symWalk, Matrix.of_apply,
        Pi.smul_apply, smul_eq_mul] at hx
      have h2 := Real.mul_self_sqrt (hdeg x).le
      have h3 := (sqrt_pos' W hdeg x).ne'
      have e1 : ∑ y, W x y * (g0 y / Real.sqrt (SteurerHDX.vdeg W y)) =
          Real.sqrt (SteurerHDX.vdeg W x) *
            ∑ y, W x y / (Real.sqrt (SteurerHDX.vdeg W x) * Real.sqrt (SteurerHDX.vdeg W y)) *
              g0 y := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        have h4 := (sqrt_pos' W hdeg y).ne'
        field_simp
      rw [e1, hx]
      field_simp
      rw [Real.sq_sqrt (hdeg x).le]; ring

end Spec

section LinkGraph
variable (X : Finset (Finset V)) (d : ℕ)

lemma wW_zero_right (hX : IsPure X d) (β : Finset V) (x y : V) (h : y ∈ β ∨ insert y β ∉ X) :
    wW X d β x y = 0 := by
  rcases h with h | h
  · unfold wW; rw [if_neg]; exact fun h' => h'.2.1 h
  · exact wW_zero_of_not_mem X d hX β x y h

lemma cW_zero_of (hX : IsPure X d) (β : Finset V) (y : V) (h : y ∈ β ∨ insert y β ∉ X) :
    cW X d β y = 0 := by
  rcases h with h | h
  · unfold cW; rw [if_neg]; exact fun h' => h' h
  · exact cW_zero_of_not_mem X d hX β y h

lemma rep (β : Finset V) (s : faces (link X β) 1) :
    ∃ x, s.1 = {x} ∧ x ∉ β ∧ insert x β ∈ X := (mem_iota X β s.1).1 s.2

lemma wLinkAdj_apply (β : Finset V) (s t : faces (link X β) 1) :
    wLinkAdj X d β s t =
      if s.1 ≠ t.1 ∧ s.1 ∪ t.1 ∈ link X β then (fc X d (β ∪ s.1 ∪ t.1) : ℝ) else 0 := by
  simp only [wLinkAdj, Matrix.of_apply, ne_eq, Subtype.ext_iff]

lemma entry_eq (hX : IsPure X d) (β : Finset V) (s t : faces (link X β) 1) (x y : V)
    (hs : s.1 = {x}) (ht : t.1 = {y}) (hx : x ∉ β) (hy : y ∉ β) :
    wLinkAdj X d β s t = wW X d β x y := by
  rw [← Phi_eq X d hX β x y hx hy, wLinkAdj_apply, hs, ht]

lemma row_sum (hX : IsPure X d) (β : Finset V) (s : faces (link X β) 1) (x : V)
    (hs : s.1 = {x}) (hx : x ∉ β) (F : Finset V → ℝ) (F' : V → ℝ) (hF : ∀ y, F {y} = F' y) :
    ∑ t : faces (link X β) 1, wLinkAdj X d β s t * F t.1 =
      ∑ y ∈ Uv X, wW X d β x y * F' y := by
  have := sum_iota2 X β
    (fun a => (if s.1 ≠ a ∧ s.1 ∪ a ∈ link X β then (fc X d (β ∪ s.1 ∪ a) : ℝ) else 0) * F a)
    (fun y => wW X d β x y * F' y)
    (by
      intro y _ hy _
      show (if s.1 ≠ {y} ∧ s.1 ∪ {y} ∈ link X β then (fc X d (β ∪ s.1 ∪ {y}) : ℝ) else 0) * F {y} = _
      rw [hs, hF y, Phi_eq X d hX β x y hx hy])
    (by
      intro y _ hy
      simp only [wW_zero_right X d hX β x y hy, zero_mul])
  rw [← this]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [wLinkAdj_apply]

lemma vdeg_eq (hX : IsPure X d) (β : Finset V) (s : faces (link X β) 1) (x : V)
    (hs : s.1 = {x}) (hx : x ∉ β) :
    vdeg (wLinkAdj X d β) s = ((d : ℝ) - β.card - 1) * cW X d β x := by
  have := row_sum X d hX β s x hs hx (fun _ => 1) (fun _ => 1) (fun _ => rfl)
  simp only [mul_one] at this
  unfold vdeg
  rw [this, sum_wW X d hX β x]

lemma two_le_card (hX : IsPure X d) (β : Finset V) (hβ : β ∈ X) (hβd : β.card + 2 ≤ d) :
    2 ≤ Fintype.card (faces (link X β) 1) := by
  obtain ⟨σ, hσ, hs⟩ := exists_facet X d hX β hβ
  obtain ⟨hσX, hσc⟩ := (mem_faces_iff X d σ).1 hσ
  have hc : 1 < (σ \ β).card := by rw [Finset.card_sdiff_of_subset hs]; omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hc
  rw [Finset.mem_sdiff] at ha hb
  have h1 : 1 < (faces (link X β) 1).card := by
    refine Finset.one_lt_card.2 ⟨{a}, ?_, {b}, ?_, by simpa using hab⟩
    · rw [mem_iota]; exact ⟨a, rfl, ha.2, hX.1 σ hσX _ (Finset.insert_subset ha.1 hs)⟩
    · rw [mem_iota]; exact ⟨b, rfl, hb.2, hX.1 σ hσX _ (Finset.insert_subset hb.1 hs)⟩
  rw [Fintype.card_coe]; omega

lemma link_structure (hX : IsPure X d) (β : Finset V) (hβ : β ∈ X) (hβd : β.card + 2 ≤ d) :
    (∀ s t : faces (link X β) 1, wLinkAdj X d β s t = wLinkAdj X d β t s) ∧
    (∀ s t : faces (link X β) 1, 0 ≤ wLinkAdj X d β s t) ∧
    (∀ s : faces (link X β) 1, 0 < vdeg (wLinkAdj X d β) s) ∧
    2 ≤ Fintype.card (faces (link X β) 1) := by
  have hmpos : 0 < (d : ℝ) - β.card - 1 := by
    have : (β.card : ℝ) + 2 ≤ d := by exact_mod_cast hβd
    linarith
  refine ⟨?_, ?_, ?_, two_le_card X d hX β hβ hβd⟩
  · intro s t
    obtain ⟨x, hx, hxb, _⟩ := rep X β s
    obtain ⟨y, hy, hyb, _⟩ := rep X β t
    rw [entry_eq X d hX β s t x y hx hy hxb hyb, entry_eq X d hX β t s y x hy hx hyb hxb,
      wW_comm]
  · intro s t
    obtain ⟨x, hx, hxb, _⟩ := rep X β s
    obtain ⟨y, hy, hyb, _⟩ := rep X β t
    rw [entry_eq X d hX β s t x y hx hy hxb hyb]
    exact wW_nonneg X d β x y
  · intro s
    obtain ⟨x, hx, hxb, hxX⟩ := rep X β s
    rw [vdeg_eq X d hX β s x hx hxb]
    refine mul_pos hmpos ?_
    unfold cW
    rw [if_pos hxb]
    exact Nat.cast_pos.2 (fc_pos X d hX _ hxX)

theorem local_ineq (hX : IsPure X d) (β : Finset V) (hβ : β ∈ X) (hβd : β.card + 2 ≤ d)
    (g : ℝ) (hg : wLam X d β ≤ g) (H : V → ℝ)
    (h0 : ∑ y ∈ Uv X, cW X d β y * H y = 0) :
    ∑ y ∈ Uv X, ∑ z ∈ Uv X, wW X d β y z * H y * H z ≤
      g * (((d : ℝ) - β.card - 1) * ∑ y ∈ Uv X, cW X d β y * H y ^ 2) := by
  obtain ⟨hsymm, hnn, hdeg, hcard⟩ := link_structure X d hX β hβ hβd
  obtain ⟨hA, -⟩ := Spec.spec_basic (wLinkAdj X d β) hsymm hnn hdeg hcard
  set m : ℝ := (d : ℝ) - β.card - 1 with hm
  have hmpos : 0 < m := by
    have : (β.card : ℝ) + 2 ≤ d := by exact_mod_cast hβd
    rw [hm]; linarith
  set h : faces (link X β) 1 → ℝ := fun s => ∑ a ∈ s.1, H a with hh
  have hhs : ∀ s x, s.1 = {x} → h s = H x := by
    intro s x hs; simp [hh, hs]
  have key0 : ∑ s, vdeg (wLinkAdj X d β) s * h s = m * ∑ y ∈ Uv X, cW X d β y * H y := by
    have := sum_iota2 X β (fun a => m * ∑ b ∈ a, cW X d β b * H b)
      (fun y => m * (cW X d β y * H y))
      (by intro y _ _ _; simp)
      (by intro y _ hy; rw [cW_zero_of X d hX β y hy]; simp)
    calc ∑ s, vdeg (wLinkAdj X d β) s * h s
        = ∑ s : faces (link X β) 1, (fun a => m * ∑ b ∈ a, cW X d β b * H b) s.1 := by
          refine Finset.sum_congr rfl fun s _ => ?_
          obtain ⟨x, hs, hx, _⟩ := rep X β s
          rw [vdeg_eq X d hX β s x hs hx, hhs s x hs]
          simp only [hs, Finset.sum_singleton]
          rw [hm]; ring
      _ = ∑ y ∈ Uv X, m * (cW X d β y * H y) := this
      _ = _ := by rw [Finset.mul_sum]
  have key1 : ∑ s, vdeg (wLinkAdj X d β) s * h s ^ 2 =
      m * ∑ y ∈ Uv X, cW X d β y * H y ^ 2 := by
    have := sum_iota2 X β (fun a => m * ∑ b ∈ a, cW X d β b * H b ^ 2)
      (fun y => m * (cW X d β y * H y ^ 2))
      (by intro y _ _ _; simp)
      (by intro y _ hy; rw [cW_zero_of X d hX β y hy]; simp)
    calc ∑ s, vdeg (wLinkAdj X d β) s * h s ^ 2
        = ∑ s : faces (link X β) 1, (fun a => m * ∑ b ∈ a, cW X d β b * H b ^ 2) s.1 := by
          refine Finset.sum_congr rfl fun s _ => ?_
          obtain ⟨x, hs, hx, _⟩ := rep X β s
          rw [vdeg_eq X d hX β s x hs hx, hhs s x hs]
          simp only [hs, Finset.sum_singleton]
          rw [hm]; ring
      _ = ∑ y ∈ Uv X, m * (cW X d β y * H y ^ 2) := this
      _ = _ := by rw [Finset.mul_sum]
  have key2 : ∑ s, ∑ t, wLinkAdj X d β s t * h s * h t =
      ∑ y ∈ Uv X, ∑ z ∈ Uv X, wW X d β y z * H y * H z := by
    have := sum_iota2 X β (fun a => ∑ b ∈ a, H b * ∑ z ∈ Uv X, wW X d β b z * H z)
      (fun y => H y * ∑ z ∈ Uv X, wW X d β y z * H z)
      (by intro y _ _ _; simp)
      (by
        intro y _ hy
        have : ∑ z ∈ Uv X, wW X d β y z * H z = 0 := by
          refine Finset.sum_eq_zero fun z _ => ?_
          rw [wW_comm, wW_zero_right X d hX β z y hy, zero_mul]
        rw [this, mul_zero])
    calc ∑ s, ∑ t, wLinkAdj X d β s t * h s * h t
        = ∑ s : faces (link X β) 1,
            (fun a => ∑ b ∈ a, H b * ∑ z ∈ Uv X, wW X d β b z * H z) s.1 := by
          refine Finset.sum_congr rfl fun s _ => ?_
          obtain ⟨x, hs, hx, _⟩ := rep X β s
          have hr := row_sum X d hX β s x hs hx (fun a => ∑ b ∈ a, H b) H (by intro y; simp)
          have : ∑ t, wLinkAdj X d β s t * h s * h t = H x * ∑ y ∈ Uv X, wW X d β x y * H y := by
            rw [← hr, Finset.mul_sum, hhs s x hs]
            refine Finset.sum_congr rfl fun t _ => ?_
            simp only [hh]
            ring
          rw [this]
          simp [hs]
      _ = ∑ y ∈ Uv X, H y * ∑ z ∈ Uv X, wW X d β y z * H z := this
      _ = _ := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          ring
  have := hA h (by rw [key0, h0, mul_zero])
  rw [key2, key1] at this
  have hlam : lambdaTwo (wLinkAdj X d β) ≤ g := hg
  have hS : 0 ≤ m * ∑ y ∈ Uv X, cW X d β y * H y ^ 2 :=
    mul_nonneg hmpos.le (Finset.sum_nonneg fun y _ => mul_nonneg (cW_nonneg X d β y) (sq_nonneg _))
  calc _ ≤ _ := this
    _ ≤ _ := mul_le_mul_of_nonneg_right hlam hS

end LinkGraph

lemma const_of_preconn {ι : Type*} (G : SimpleGraph ι) (hc : G.Preconnected) (f : ι → ℝ)
    (h : ∀ a b, G.Adj a b → f a = f b) : ∀ a b, f a = f b := by
  intro a b
  obtain ⟨p⟩ := hc a b
  induction p with
  | nil => rfl
  | cons hadj p ih => exact (h _ _ hadj).trans ih

section Eigen
variable (X : Finset (Finset V)) (d : ℕ)

theorem eigen_V (hX : IsPure X d) (α : Finset V) (hα : α ∈ X) (hαd : α.card + 2 ≤ d) :
    ∃ H : V → ℝ,
      ∑ y ∈ Uv X, cW X d α y * H y = 0 ∧
      0 < ∑ y ∈ Uv X, cW X d α y * H y ^ 2 ∧
      (∀ x, ∑ y ∈ Uv X, wW X d α x y * H y =
        wLam X d α * (((d : ℝ) - α.card - 1) * cW X d α x) * H x) ∧
      ((skeleton1 (link X α)).Connected →
        (∀ x ∈ Uv X, ∀ y ∈ Uv X, 0 < wW X d α x y → H x = H y) →
        ∀ x y, 0 < cW X d α x → 0 < cW X d α y → H x = H y) := by
  obtain ⟨hsymm, hnn, hdeg, hcard⟩ := link_structure X d hX α hα hαd
  obtain ⟨-, f, hf0, hf1, hf2⟩ := Spec.spec_basic (wLinkAdj X d α) hsymm hnn hdeg hcard
  set m : ℝ := (d : ℝ) - α.card - 1 with hm
  have hmpos : 0 < m := by
    have : (α.card : ℝ) + 2 ≤ d := by exact_mod_cast hαd
    rw [hm]; linarith
  let H : V → ℝ := fun x =>
    if hx : ({x} : Finset V) ∈ faces (link X α) 1 then f ⟨{x}, hx⟩ else 0
  have hHs : ∀ (s : faces (link X α) 1) x, s.1 = {x} → H x = f s := by
    intro s x hs
    have hx : ({x} : Finset V) ∈ faces (link X α) 1 := by rw [← hs]; exact s.2
    have : (⟨{x}, hx⟩ : faces (link X α) 1) = s := Subtype.ext hs.symm
    simp only [H, dif_pos hx, this]
  have hfH : ∀ s : faces (link X α) 1, f s = ∑ b ∈ s.1, H b := by
    intro s
    obtain ⟨x, hs, _, _⟩ := rep X α s
    rw [hs, Finset.sum_singleton, hHs s x hs]
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · -- E1
    have := sum_iota2 X α (fun a => m * ∑ b ∈ a, cW X d α b * H b)
      (fun y => m * (cW X d α y * H y))
      (by intro y _ _ _; simp)
      (by intro y _ hy; rw [cW_zero_of X d hX α y hy]; simp)
    have e : ∑ s, vdeg (wLinkAdj X d α) s * f s =
        ∑ y ∈ Uv X, m * (cW X d α y * H y) := by
      rw [← this]
      refine Finset.sum_congr rfl fun s _ => ?_
      obtain ⟨x, hs, hx, _⟩ := rep X α s
      rw [vdeg_eq X d hX α s x hs hx, ← hHs s x hs]
      simp only [hs, Finset.sum_singleton]
      rw [hm]; ring
    rw [e, ← Finset.mul_sum] at hf1
    rcases mul_eq_zero.1 hf1 with h | h
    · exact absurd h hmpos.ne'
    · exact h
  · -- E3
    obtain ⟨s, hs⟩ : ∃ s, f s ≠ 0 := by
      by_contra h
      push Not at h
      exact hf0 (funext h)
    obtain ⟨x, hxs, hxα, hxX⟩ := rep X α s
    have hHx : H x ≠ 0 := by rw [hHs s x hxs]; exact hs
    have hxU : x ∈ Uv X := subset_Uv X _ hxX (Finset.mem_insert_self _ _)
    have hc : 0 < cW X d α x := by
      unfold cW; rw [if_pos hxα]; exact Nat.cast_pos.2 (fc_pos X d hX _ hxX)
    have hle := Finset.single_le_sum (f := fun y => cW X d α y * H y ^ 2)
      (fun y _ => mul_nonneg (cW_nonneg X d α y) (sq_nonneg _)) hxU
    exact lt_of_lt_of_le (mul_pos hc (by positivity)) hle
  · -- E2
    intro x
    by_cases hP : x ∉ α ∧ insert x α ∈ X
    · have hxm : ({x} : Finset V) ∈ faces (link X α) 1 := (mem_iota X α _).2 ⟨x, rfl, hP.1, hP.2⟩
      set s : faces (link X α) 1 := ⟨{x}, hxm⟩ with hsdef
      have hs : s.1 = {x} := rfl
      have h2 := hf2 s
      have hr := row_sum X d hX α s x hs hP.1 (fun a => ∑ b ∈ a, H b) H (by intro y; simp)
      have e : ∑ y, wLinkAdj X d α s y * f y =
          ∑ t : faces (link X α) 1, wLinkAdj X d α s t * (fun a => ∑ b ∈ a, H b) t.1 :=
        Finset.sum_congr rfl fun t _ => by rw [hfH t]
      rw [e, hr, vdeg_eq X d hX α s x hs hP.1, ← hHs s x hs] at h2
      unfold wLam
      rw [h2]
    · have hP' : x ∈ α ∨ insert x α ∉ X := by
        by_cases h : x ∈ α
        · exact Or.inl h
        · right; intro h'; exact hP ⟨h, h'⟩
      rw [cW_zero_of X d hX α x hP']
      have : ∀ y ∈ Uv X, wW X d α x y * H y = 0 := by
        intro y _
        rw [wW_comm, wW_zero_right X d hX α y x hP', zero_mul]
      rw [Finset.sum_eq_zero this]
      simp
  · -- E4
    intro hconn hadj x y hx hy
    have hxP : x ∉ α ∧ insert x α ∈ X := by
      unfold cW at hx
      by_cases h : x ∈ α
      · rw [if_neg (not_not.2 h)] at hx; exact absurd hx (lt_irrefl _)
      · rw [if_pos h] at hx
        exact ⟨h, fc_ne_zero_mem X d hX _ (by exact_mod_cast hx.ne')⟩
    have hyP : y ∉ α ∧ insert y α ∈ X := by
      unfold cW at hy
      by_cases h : y ∈ α
      · rw [if_neg (not_not.2 h)] at hy; exact absurd hy (lt_irrefl _)
      · rw [if_pos h] at hy
        exact ⟨h, fc_ne_zero_mem X d hX _ (by exact_mod_cast hy.ne')⟩
    have hconst := const_of_preconn (skeleton1 (link X α)) hconn.preconnected f (by
      intro s t hst
      obtain ⟨u, hu, hub, huX⟩ := rep X α s
      obtain ⟨v, hv, hvb, hvX⟩ := rep X α t
      have hl : s.1 ∪ t.1 ∈ link X α := hst.2
      have hmem := union_mem_link X α _ hl
      rw [hu, hv] at hmem
      have hset : α ∪ ({u} ∪ {v}) = insert u (insert v α) := by
        ext w; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto
      rw [hset] at hmem
      have hne : u ≠ v := by
        intro e; apply hst.1; apply Subtype.ext; rw [hu, hv, e]
      have hpos : 0 < wW X d α u v := by
        unfold wW
        rw [if_pos ⟨hub, hvb, hne⟩]
        exact Nat.cast_pos.2 (fc_pos X d hX _ hmem)
      rw [← hHs s u hu, ← hHs t v hv]
      exact hadj u (subset_Uv X _ huX (Finset.mem_insert_self _ _)) v
        (subset_Uv X _ hvX (Finset.mem_insert_self _ _)) hpos)
    have hxm : ({x} : Finset V) ∈ faces (link X α) 1 := (mem_iota X α _).2 ⟨x, rfl, hxP.1, hxP.2⟩
    have hym : ({y} : Finset V) ∈ faces (link X α) 1 := (mem_iota X α _).2 ⟨y, rfl, hyP.1, hyP.2⟩
    rw [hHs ⟨{x}, hxm⟩ x rfl, hHs ⟨{y}, hym⟩ y rfl]
    exact hconst _ _

end Eigen

lemma quad_expand (U : Finset V) (w : V → V → ℝ) (hsym : ∀ y z, w y z = w z y)
    (c : V → ℝ) (r : ℝ) (hrow : ∀ y, ∑ z ∈ U, w y z = r * c y) (H : V → ℝ) (μ : ℝ) :
    ∑ y ∈ U, ∑ z ∈ U, w y z * (H y - μ) * (H z - μ) =
      ∑ y ∈ U, ∑ z ∈ U, w y z * H y * H z - 2 * μ * r * ∑ y ∈ U, c y * H y +
        μ ^ 2 * r * ∑ y ∈ U, c y := by
  have t1 : ∑ y ∈ U, ∑ z ∈ U, w y z * H y = r * ∑ y ∈ U, c y * H y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul, hrow y]; ring
  have t2 : ∑ y ∈ U, ∑ z ∈ U, w y z * H z = r * ∑ y ∈ U, c y * H y := by
    rw [Finset.sum_comm, ← t1]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by rw [hsym z y]
  have t3 : ∑ y ∈ U, ∑ z ∈ U, w y z = r * ∑ y ∈ U, c y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => hrow y
  have e1 : ∀ y z, w y z * (H y - μ) * (H z - μ) =
      w y z * H y * H z - μ * (w y z * H y) - μ * (w y z * H z) + μ ^ 2 * w y z := by
    intro y z; ring
  simp only [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [t1, t2, t3]
  ring

lemma wW_zero_of_base (X : Finset (Finset V)) (d : ℕ) (hX : IsPure X d) (γ : Finset V) (h : γ ∉ X) (y z : V) :
    wW X d γ y z = 0 := by
  unfold wW
  split_ifs
  · have := fc_zero_of_sub X d hX γ (insert y (insert z γ))
      ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _)) h
    simp [this]
  · rfl

lemma sum_filter_notin (U : Finset V) (α : Finset V) (T : V → ℝ) (hT : ∀ x ∈ α, T x = 0) :
    ∑ x ∈ U.filter (fun x => x ∉ α), T x = ∑ x ∈ U, T x := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : x ∈ α
  · rw [if_neg (not_not.2 h), hT x h]
  · rw [if_pos h]

/-- W1: Oppenheim's trickling-down (Garland method), weighted form.  Needs the link of `α`
to have facets of size >= 3 (`α.card + 3 ≤ d`), `α`-link connected, all vertex-link graphs
`≤ g < 1`. -/
theorem trickle_step (X : Finset (Finset V)) (d : ℕ) (hX : IsPure X d) (α : Finset V)
    (hα : α ∈ X) (hd : α.card + 3 ≤ d)
    (hconn : (skeleton1 (link X α)).Connected) (g : ℝ) (hg : g < 1)
    (hβ : ∀ β ∈ X, α ⊆ β → β.card = α.card + 1 → wLam X d β ≤ g) :
    wLam X d α ≤ g / (1 - g) := by
  have hαd : α.card + 2 ≤ d := by omega
  obtain ⟨H, E1, E3, E2, E4⟩ := eigen_V X d hX α hα hαd
  set lam : ℝ := wLam X d α with hlam
  set m : ℝ := (d : ℝ) - α.card - 1 with hm
  have hcd : (α.card : ℝ) + 3 ≤ d := by exact_mod_cast hd
  have hm1 : 0 < m - 1 := by rw [hm]; linarith
  have hmpos : 0 < m := by linarith
  set Nc : ℝ := ∑ y ∈ Uv X, cW X d α y * H y ^ 2 with hNc
  have hmN : 0 < m * Nc := mul_pos hmpos E3
  -- Q
  set Q : ℝ := ∑ y ∈ Uv X, ∑ z ∈ Uv X, wW X d α y z * H y * H z with hQ
  have hQeq : Q = lam * (m * Nc) := by
    have : Q = ∑ y ∈ Uv X, H y * ∑ z ∈ Uv X, wW X d α y z * H z := by
      rw [hQ]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      ring
    rw [this, hNc, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [E2 y]
    ring
  -- D
  have hT1 : ∑ y ∈ Uv X, ∑ z ∈ Uv X, wW X d α y z * H y ^ 2 = m * Nc := by
    rw [hNc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul, sum_wW X d hX α y]
    ring
  have hT2 : ∑ y ∈ Uv X, ∑ z ∈ Uv X, wW X d α y z * H z ^ 2 = m * Nc := by
    rw [Finset.sum_comm, ← hT1]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by
      rw [wW_comm X d α z y]
  have hD : ∑ y ∈ Uv X, ∑ z ∈ Uv X, wW X d α y z * (H y - H z) ^ 2 =
      2 * (m * Nc) - 2 * Q := by
    have e : ∀ y z, wW X d α y z * (H y - H z) ^ 2 =
        wW X d α y z * H y ^ 2 + wW X d α y z * H z ^ 2 - 2 * (wW X d α y z * H y * H z) := by
      intro y z; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hT1, hT2, hQ]
    ring
  have hDnn : ∀ y ∈ Uv X, ∀ z ∈ Uv X, 0 ≤ wW X d α y z * (H y - H z) ^ 2 :=
    fun y _ z _ => mul_nonneg (wW_nonneg X d α y z) (sq_nonneg _)
  have hD0 : 0 ≤ ∑ y ∈ Uv X, ∑ z ∈ Uv X, wW X d α y z * (H y - H z) ^ 2 :=
    Finset.sum_nonneg fun y hy => Finset.sum_nonneg fun z hz => hDnn y hy z hz
  have hlam1 : lam ≤ 1 := by
    rw [hD, hQeq] at hD0
    nlinarith
  have hlam_lt : lam < 1 := by
    refine lt_of_le_of_ne hlam1 ?_
    intro h1
    have hD' : ∑ y ∈ Uv X, ∑ z ∈ Uv X, wW X d α y z * (H y - H z) ^ 2 = 0 := by
      rw [hD, hQeq, h1]; ring
    have hrow := (Finset.sum_eq_zero_iff_of_nonneg
      (fun y hy => Finset.sum_nonneg fun z hz => hDnn y hy z hz)).1 hD'
    have hadj : ∀ x ∈ Uv X, ∀ y ∈ Uv X, 0 < wW X d α x y → H x = H y := by
      intro x hx y hy hpos
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun z hz => hDnn x hx z hz)).1
        (hrow x hx) y hy
      have : (H x - H y) ^ 2 = 0 := by
        rcases mul_eq_zero.1 h2 with h | h
        · exact absurd h hpos.ne'
        · exact h
      have := pow_eq_zero_iff (two_ne_zero) |>.1 this
      linarith
    have hconst := E4 hconn hadj
    -- pick x0 with cW > 0 and H x0 ≠ 0
    obtain ⟨x0, hx0U, hx0⟩ : ∃ x ∈ Uv X, 0 < cW X d α x * H x ^ 2 := by
      by_contra hcon
      push Not at hcon
      have : Nc ≤ 0 := Finset.sum_nonpos hcon
      linarith
    have hc0 : 0 < cW X d α x0 := by
      by_contra hc
      have : cW X d α x0 = 0 := le_antisymm (not_lt.1 hc) (cW_nonneg X d α x0)
      rw [this] at hx0; simp at hx0
    have hsum : ∑ y ∈ Uv X, cW X d α y * H y = H x0 * ∑ y ∈ Uv X, cW X d α y := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hy : 0 < cW X d α y
      · rw [hconst y x0 hy hc0]; ring
      · have : cW X d α y = 0 := le_antisymm (not_lt.1 hy) (cW_nonneg X d α y)
        rw [this]; ring
    have hcpos : 0 < ∑ y ∈ Uv X, cW X d α y :=
      lt_of_lt_of_le hc0 (Finset.single_le_sum (f := fun y => cW X d α y)
        (fun y _ => cW_nonneg X d α y) hx0U)
    rw [E1] at hsum
    have hH0 : H x0 = 0 := by
      rcases mul_eq_zero.1 hsum.symm with h | h
      · exact h
      · exact absurd h hcpos.ne'
    rw [hH0] at hx0; simp at hx0
  -- local inequalities
  have hloc : ∀ x ∈ (Uv X).filter (fun x => x ∉ α),
      ∑ y ∈ Uv X, ∑ z ∈ Uv X, wW X d (insert x α) y z * H y * H z ≤
        (m - 1) * ((1 - g) * ((m * cW X d α x) * (lam * H x) ^ 2) +
          g * ∑ y ∈ Uv X, wW X d α x y * H y ^ 2) := by
    intro x hx
    have hxα : x ∉ α := (Finset.mem_filter.1 hx).2
    by_cases hxX : insert x α ∈ X
    · set β := insert x α with hβdef
      have hβc : β.card = α.card + 1 := Finset.card_insert_of_notMem hxα
      have hβd : β.card + 2 ≤ d := by omega
      have hloc0 := local_ineq X d hX β hxX hβd g (hβ β hxX (Finset.subset_insert _ _) hβc)
        (fun y => H y - lam * H x) (by
          have : ∀ y, cW X d β y = wW X d α x y := fun y => cW_insert X d α x y hxα
          simp only [this]
          have e : ∀ y, wW X d α x y * (H y - lam * H x) =
              wW X d α x y * H y - lam * H x * wW X d α x y := by intro y; ring
          simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, E2 x, sum_wW X d hX α x]
          ring)
      have hbm : (d : ℝ) - β.card - 1 = m - 1 := by rw [hβc, hm]; push_cast; ring
      rw [hbm] at hloc0
      have hrow : ∀ y, ∑ z ∈ Uv X, wW X d β y z = (m - 1) * cW X d β y := by
        intro y; rw [sum_wW X d hX β y, hbm]
      have hex := quad_expand (Uv X) (wW X d β) (wW_comm X d β) (cW X d β) (m - 1) hrow H
        (lam * H x)
      have hc1 : ∀ y, cW X d β y = wW X d α x y := fun y => cW_insert X d α x y hxα
      have hs1 : ∑ y ∈ Uv X, cW X d β y * H y = lam * (m * cW X d α x) * H x := by
        simp only [hc1]; exact E2 x
      have hs0 : ∑ y ∈ Uv X, cW X d β y = m * cW X d α x := by
        simp only [hc1]; exact sum_wW X d hX α x
      have hs2 : ∑ y ∈ Uv X, cW X d β y * (H y - lam * H x) ^ 2 =
          ∑ y ∈ Uv X, wW X d α x y * H y ^ 2 - (lam * H x) ^ 2 * (m * cW X d α x) := by
        have e : ∀ y, cW X d β y * (H y - lam * H x) ^ 2 =
            cW X d β y * H y ^ 2 - 2 * (lam * H x) * (cW X d β y * H y) +
              (lam * H x) ^ 2 * cW X d β y := by intro y; ring
        have hs3 : ∑ y ∈ Uv X, cW X d β y * H y ^ 2 = ∑ y ∈ Uv X, wW X d α x y * H y ^ 2 := by
          simp only [hc1]
        simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hs1, hs0,
          hs3]
        ring
      rw [hex, hs1, hs0] at hloc0
      rw [hs2] at hloc0
      nlinarith [hloc0]
    · have h1 : ∀ y ∈ Uv X, ∀ z ∈ Uv X, wW X d (insert x α) y z * H y * H z = 0 := by
        intro y _ z _
        rw [wW_zero_of_base X d hX _ hxX, zero_mul, zero_mul]
      rw [Finset.sum_eq_zero fun y hy => Finset.sum_eq_zero fun z hz => h1 y hy z hz]
      have hP' : x ∈ α ∨ insert x α ∉ X := Or.inr hxX
      have h2 : ∀ y ∈ Uv X, wW X d α x y * H y ^ 2 = 0 := by
        intro y _
        rw [wW_comm, wW_zero_right X d hX α y x hP', zero_mul]
      rw [Finset.sum_eq_zero h2, cW_zero_of X d hX α x hP']
      simp
  have hsum := Finset.sum_le_sum hloc
  have hSA : ∑ x ∈ (Uv X).filter (fun x => x ∉ α),
      ∑ y ∈ Uv X, ∑ z ∈ Uv X, wW X d (insert x α) y z * H y * H z = (m - 1) * Q := by
    have e : ∀ y z, ∑ x ∈ (Uv X).filter (fun x => x ∉ α), wW X d (insert x α) y z * H y * H z =
        (m - 1) * (wW X d α y z * H y * H z) := by
      intro y z
      rw [← Finset.sum_mul, ← Finset.sum_mul, sum_wW_ext X d hX α y z, hm]
      ring
    rw [Finset.sum_comm]
    have e2 : ∀ y ∈ Uv X, ∑ x ∈ (Uv X).filter (fun x => x ∉ α),
        ∑ z ∈ Uv X, wW X d (insert x α) y z * H y * H z =
        ∑ z ∈ Uv X, ∑ x ∈ (Uv X).filter (fun x => x ∉ α),
          wW X d (insert x α) y z * H y * H z := fun y _ => Finset.sum_comm
    rw [Finset.sum_congr rfl e2]
    simp only [e, ← Finset.mul_sum]
    rw [hQ]
  have hS2 : ∑ x ∈ (Uv X).filter (fun x => x ∉ α),
      ∑ y ∈ Uv X, wW X d α x y * H y ^ 2 = m * Nc := by
    rw [sum_filter_notin (Uv X) α _ (by
      intro x hx
      refine Finset.sum_eq_zero fun y _ => ?_
      unfold wW
      rw [if_neg (fun h => h.1 hx), zero_mul])]
    exact hT2
  have hS1 : ∑ x ∈ (Uv X).filter (fun x => x ∉ α), (m * cW X d α x) * (lam * H x) ^ 2 =
      lam ^ 2 * (m * Nc) := by
    rw [sum_filter_notin (Uv X) α _ (by
      intro x hx
      rw [cW_zero_of X d hX α x (Or.inl hx)]; ring)]
    rw [hNc, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hrhs : ∑ x ∈ (Uv X).filter (fun x => x ∉ α),
      (m - 1) * ((1 - g) * ((m * cW X d α x) * (lam * H x) ^ 2) +
        g * ∑ y ∈ Uv X, wW X d α x y * H y ^ 2) =
      (m - 1) * ((1 - g) * (lam ^ 2 * (m * Nc)) + g * (m * Nc)) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hS1, hS2]
  rw [hSA, hrhs, hQeq] at hsum
  have hkey0 := le_of_mul_le_mul_left hsum (by linarith : (0 : ℝ) < m - 1)
  have hkey : lam ≤ (1 - g) * lam ^ 2 + g := by
    by_contra h
    push Not at h
    have := mul_lt_mul_of_pos_right h hmN
    nlinarith
  rw [le_div_iff₀ (by linarith)]
  by_contra hcon
  push Not at hcon
  nlinarith [mul_pos (sub_pos.2 hlam_lt) (sub_pos.2 hcon)]
namespace LG

variable (X : Finset (Finset V)) (d : ℕ)

lemma mem_of_sub (hX : IsPure X d) {a c : Finset V} (ha : a ∈ X) (hc : c ⊆ a) : c ∈ X :=
  hX.1 a ha c hc

lemma ext_facet (hX : IsPure X d) {a : Finset V} (ha : a ∈ X) :
    ∃ σ ∈ faces X d, a ⊆ σ := by
  obtain ⟨σ, hσ, hmax⟩ := Finset.exists_maximal
    (s := X.filter (fun ρ => a ⊆ ρ)) ⟨a, by simp [ha]⟩
  obtain ⟨hσX, haσ⟩ := Finset.mem_filter.1 hσ
  refine ⟨σ, ?_, haσ⟩
  refine Finset.mem_filter.2 ⟨hσX, hX.2 σ hσX ?_⟩
  intro ρ hρ hσρ
  exact (hmax (Finset.mem_filter.2 ⟨hρ, haσ.trans hσρ⟩) hσρ).antisymm hσρ

lemma fc_pos (hX : IsPure X d) {a : Finset V} (ha : a ∈ X) : (1 : ℝ) ≤ (fc X d a : ℝ) := by
  obtain ⟨σ, hσ, haσ⟩ := ext_facet X d hX ha
  have : 0 < fc X d a := Finset.card_pos.2 ⟨σ, Finset.mem_filter.2 ⟨hσ, haσ⟩⟩
  exact_mod_cast this

lemma card_le (hX : IsPure X d) {a : Finset V} (ha : a ∈ X) : a.card ≤ d := by
  obtain ⟨σ, hσ, haσ⟩ := ext_facet X d hX ha
  have := (Finset.mem_filter.1 hσ).2
  rw [← this]; exact Finset.card_le_card haσ

lemma card_between (hX : IsPure X d) {σ c : Finset V} (hσ : σ ∈ faces X d) (i : ℕ)
    (hc : c.card = i) (hcσ : c ⊆ σ) :
    ((faces X (i + 1)).filter (fun a => c ⊆ a ∧ a ⊆ σ)).card = d - i := by
  have hσX := (Finset.mem_filter.1 hσ).1
  have hσd := (Finset.mem_filter.1 hσ).2
  have : (faces X (i + 1)).filter (fun a => c ⊆ a ∧ a ⊆ σ) = (σ \ c).image (fun x => insert x c) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_sdiff, faces]
    constructor
    · rintro ⟨⟨_, hac⟩, hca, haσ⟩
      have h1 : (a \ c).card = 1 := by
        rw [Finset.card_sdiff_of_subset hca, hac, hc]; omega
      obtain ⟨x, hx⟩ := Finset.card_eq_one.1 h1
      have hxm : x ∈ a \ c := by rw [hx]; simp
      rw [Finset.mem_sdiff] at hxm
      refine ⟨x, ⟨haσ hxm.1, hxm.2⟩, ?_⟩
      ext y
      simp only [Finset.mem_insert]
      constructor
      · rintro (rfl | hy)
        · exact hxm.1
        · exact hca hy
      · intro hy
        by_cases hyc : y ∈ c
        · exact Or.inr hyc
        · left
          have : y ∈ a \ c := Finset.mem_sdiff.2 ⟨hy, hyc⟩
          rw [hx] at this; simpa using this
    · rintro ⟨x, ⟨hxσ, hxc⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, Finset.subset_insert _ _, ?_⟩
      · exact hX.1 σ hσX _ (Finset.insert_subset hxσ hcσ)
      · rw [Finset.card_insert_of_notMem hxc, hc]
      · exact Finset.insert_subset hxσ hcσ
  rw [this, Finset.card_image_of_injOn, Finset.card_sdiff_of_subset hcσ, hσd, hc]
  intro x hx y hy hxy
  simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe] at hx hy
  have hxy' : insert x c = insert y c := hxy
  have : x ∈ insert y c := by rw [← hxy']; simp
  rcases Finset.mem_insert.1 this with h | h
  · exact h
  · exact absurd h hx.2

/-- I2: up-sum of facet counts. -/
lemma sum_up (hX : IsPure X d) {c : Finset V} (hc : c ∈ X) (i : ℕ) (hci : c.card = i) :
    ∑ a ∈ faces X (i + 1), (if c ⊆ a then (fc X d a : ℝ) else 0) = ((d : ℝ) - i) * (fc X d c : ℝ) := by
  have hid : i ≤ d := hci ▸ card_le X d hX hc
  have h1 : ∀ a, (if c ⊆ a then (fc X d a : ℝ) else 0) =
      ∑ σ ∈ faces X d, (if c ⊆ a ∧ a ⊆ σ then (1 : ℝ) else 0) := by
    intro a
    by_cases hca : c ⊆ a
    · simp only [hca, true_and, if_true, fc]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    · simp [hca]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ σ ∈ faces X d, ∑ a ∈ faces X (i + 1), (if c ⊆ a ∧ a ⊆ σ then (1 : ℝ) else 0) =
      if c ⊆ σ then ((d : ℝ) - i) else 0 := by
    intro σ hσ
    by_cases hcσ : c ⊆ σ
    · rw [if_pos hcσ, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
        card_between X d hX hσ i hci hcσ]
      rw [Nat.cast_sub hid]
    · rw [if_neg hcσ]
      exact Finset.sum_eq_zero fun a _ => by
        have : ¬ (c ⊆ a ∧ a ⊆ σ) := fun h => hcσ (h.1.trans h.2)
        simp [this]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rfl

lemma card_sub (hX : IsPure X d) {a : Finset V} (ha : a ∈ X) (i : ℕ) :
    ((faces X i).filter (fun c => c ⊆ a)).card = a.card.choose i := by
  have : (faces X i).filter (fun c => c ⊆ a) = Finset.powersetCard i a := by
    ext c
    simp only [faces, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨⟨mem_of_sub X d hX ha h2, h1⟩, h2⟩
  rw [this, Finset.card_powersetCard]


section local_lemma

variable {ι : Type*} [Fintype ι]

lemma E_expand (A : Matrix ι ι ℝ) (hsymm : ∀ x y, A x y = A y x)
    (hdeg : ∀ x, 0 < vdeg A x) (g : ι → ℝ) :
    GibbsCongestion.dirichletForm (walk A) (statDist A) g g =
      (1 / ∑ y, vdeg A y) * (∑ x, vdeg A x * g x ^ 2 - ∑ x, ∑ y, A x y * g x * g y) := by
  unfold GibbsCongestion.dirichletForm walk statDist
  simp only [Matrix.of_apply]
  have h1 : ∀ x y, vdeg A x / (∑ y, vdeg A y) * (A x y / vdeg A x) * (g x - g y) * (g x - g y) =
      (1 / ∑ y, vdeg A y) * (A x y * (g x ^ 2 - 2 * g x * g y + g y ^ 2)) := by
    intro x y
    have := (hdeg x).ne'
    field_simp
    ring
  simp_rw [h1]
  have hA : ∀ x, ∑ y, A x y * (g x ^ 2 - 2 * g x * g y + g y ^ 2) =
      vdeg A x * g x ^ 2 - 2 * ∑ y, A x y * g x * g y + ∑ y, A x y * g y ^ 2 := by
    intro x
    unfold vdeg
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  simp_rw [← Finset.mul_sum, hA]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  have hB : ∑ x, ∑ y, A x y * g y ^ 2 = ∑ x, vdeg A x * g x ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold vdeg
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by rw [hsymm x y]
  rw [hB]
  ring

lemma Var_expand [Nonempty ι] (A : Matrix ι ι ℝ) (hdeg : ∀ x, 0 < vdeg A x) (g : ι → ℝ) :
    variance A g = (1 / ∑ y, vdeg A y) * ∑ x, vdeg A x * g x ^ 2 -
      (∑ x, vdeg A x * g x) ^ 2 / (∑ y, vdeg A y) ^ 2 := by
  unfold variance statDist
  have hD : 0 < ∑ y, vdeg A y :=
    Finset.sum_pos (fun x _ => hdeg x) ⟨Classical.arbitrary ι, by simp⟩
  set D := ∑ y, vdeg A y with hDdef
  have hp : ∑ y, vdeg A y / D = 1 := by
    rw [← Finset.sum_div, div_self hD.ne']
  have h2 : ∀ x y, vdeg A x / D * (vdeg A y / D) * (g x - g y) ^ 2 =
      (vdeg A x / D * g x ^ 2) * (vdeg A y / D) + (vdeg A x / D) * (vdeg A y / D * g y ^ 2)
        - 2 * ((vdeg A x / D * g x) * (vdeg A y / D * g y)) := by
    intro x y; ring
  simp_rw [h2]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    hp, ← Finset.mul_sum]
  have e1 : ∑ i, vdeg A i / D * g i ^ 2 = (∑ x, vdeg A x * g x ^ 2) / D := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, vdeg A i / D * g i = (∑ x, vdeg A x * g x) / D := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hp, e1, e2]
  field_simp
  ring


lemma local_ineq (A : Matrix ι ι ℝ) (hcard : 2 ≤ Fintype.card ι)
    (hsymm : ∀ x y, A x y = A y x) (hnn : ∀ x y, 0 ≤ A x y) (hdeg : ∀ x, 0 < vdeg A x)
    (γ : ℝ) (hγ : lambdaTwo A ≤ γ) (g : ι → ℝ) :
    ∑ x, ∑ y, A x y * g x * g y ≤
      γ * ∑ x, vdeg A x * g x ^ 2 + (1 - γ) * (∑ x, vdeg A x * g x) ^ 2 / ∑ x, vdeg A x := by
  have hne : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hD : 0 < ∑ y, vdeg A y :=
    Finset.sum_pos (fun x _ => hdeg x) ⟨Classical.arbitrary ι, by simp⟩
  set D := ∑ y, vdeg A y with hDdef
  by_cases hconst : ∃ x y, g x ≠ g y
  · obtain ⟨x0, y0, hxy⟩ := hconst
    have hL := SteurerHDX.lemma_2_1 A hcard hsymm hnn hdeg
    have hmem := hL.2.2 ⟨g, ⟨x0, y0, hxy⟩, rfl⟩
    have hVpos : 0 < variance A g := by
      unfold variance
      have hπ : ∀ x, 0 < statDist A x := fun x => div_pos (hdeg x) hD
      have hterm : ∀ x y, 0 ≤ statDist A x * statDist A y * (g x - g y) ^ 2 :=
        fun x y => by have := hπ x; have := hπ y; positivity
      have h1 : statDist A x0 * statDist A y0 * (g x0 - g y0) ^ 2 ≤
          ∑ y, statDist A x0 * statDist A y * (g x0 - g y) ^ 2 :=
        Finset.single_le_sum (f := fun y => statDist A x0 * statDist A y * (g x0 - g y) ^ 2)
          (fun y _ => hterm x0 y) (Finset.mem_univ y0)
      have h2 : ∑ y, statDist A x0 * statDist A y * (g x0 - g y) ^ 2 ≤
          ∑ x, ∑ y, statDist A x * statDist A y * (g x - g y) ^ 2 :=
        Finset.single_le_sum (f := fun x => ∑ y, statDist A x * statDist A y * (g x - g y) ^ 2)
          (fun x _ => Finset.sum_nonneg fun y _ => hterm x y) (Finset.mem_univ x0)
      have h3 : 0 < statDist A x0 * statDist A y0 * (g x0 - g y0) ^ 2 := by
        have := hπ x0; have := hπ y0
        have : (g x0 - g y0) ^ 2 > 0 := by
          have : g x0 - g y0 ≠ 0 := sub_ne_zero.2 hxy
          positivity
        positivity
      linarith
    have h1 : (1 - γ) ≤ GibbsCongestion.dirichletForm (walk A) (statDist A) g g / variance A g := by
      have : 1 - γ ≤ 1 - lambdaTwo A := by linarith
      exact this.trans hmem
    rw [le_div_iff₀ hVpos] at h1
    rw [E_expand A hsymm hdeg, Var_expand A hdeg] at h1
    have e : D * ((1 - γ) * ((1 / D) * ∑ x, vdeg A x * g x ^ 2 - (∑ x, vdeg A x * g x) ^ 2 / D ^ 2))
        = (1 - γ) * (∑ x, vdeg A x * g x ^ 2 - (∑ x, vdeg A x * g x) ^ 2 / D) := by
      field_simp
    have e' : D * ((1 / D) * (∑ x, vdeg A x * g x ^ 2 - ∑ x, ∑ y, A x y * g x * g y)) =
        ∑ x, vdeg A x * g x ^ 2 - ∑ x, ∑ y, A x y * g x * g y := by
      field_simp
    have h2 := mul_le_mul_of_nonneg_left h1 hD.le
    rw [e, e'] at h2
    have e3 : (1 - γ) * (∑ x, vdeg A x * g x) ^ 2 / D = (1 - γ) * ((∑ x, vdeg A x * g x) ^ 2 / D) := by
      ring
    rw [e3]
    nlinarith
  · push Not at hconst
    obtain ⟨c, hc⟩ : ∃ c, ∀ x, g x = c := ⟨g (Classical.arbitrary ι), fun x => hconst x _⟩
    have hG : ∑ x, ∑ y, A x y * g x * g y = D * c ^ 2 := by
      simp only [hc]
      rw [hDdef]; unfold vdeg
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun y _ => by ring
    have hS : ∑ x, vdeg A x * g x ^ 2 = D * c ^ 2 := by
      simp only [hc]; rw [← Finset.sum_mul]
    have hT : ∑ x, vdeg A x * g x = D * c := by
      simp only [hc]; rw [← Finset.sum_mul]
    rw [hG, hS, hT]
    field_simp
    nlinarith

end local_lemma

section link_bridge

variable (X : Finset (Finset V)) (d : ℕ)

lemma link_vertex (α : Finset V) (x : faces (link X α) 1) :
    α ∪ x.1 ∈ X ∧ Disjoint α x.1 ∧ x.1.card = 1 := by
  obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 x.2
  obtain ⟨σ, hσ, hσx⟩ := Finset.mem_image.1 hx1
  obtain ⟨hσX, hασ⟩ := Finset.mem_filter.1 hσ
  refine ⟨?_, ?_, hx2⟩
  · rw [← hσx, Finset.union_sdiff_of_subset hασ]; exact hσX
  · rw [← hσx]; exact Finset.disjoint_sdiff

/-- the bijection between vertices of the link and the `j`-faces containing `α` -/
lemma sum_vertices (α : Finset V) (hα : α ∈ X) (F : Finset V → ℝ) :
    ∑ x : faces (link X α) 1, F (α ∪ x.1) =
      ∑ a ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a), F a := by
  refine Finset.sum_bij (fun x _ => α ∪ x.1) ?_ ?_ ?_ ?_
  · intro x _
    obtain ⟨h1, h2, h3⟩ := link_vertex X α x
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨h1, ?_⟩, Finset.subset_union_left⟩
    rw [Finset.card_union_of_disjoint h2, h3]
  · intro x _ y _ hxy
    obtain ⟨_, h2, _⟩ := link_vertex X α x
    obtain ⟨_, h2', _⟩ := link_vertex X α y
    apply Subtype.ext
    have h : (α ∪ x.1) \ α = (α ∪ y.1) \ α := by rw [hxy]
    rwa [Finset.union_sdiff_cancel_left h2, Finset.union_sdiff_cancel_left h2'] at h
  · intro a ha
    obtain ⟨ha1, haα⟩ := Finset.mem_filter.1 ha
    obtain ⟨haX, hac⟩ := Finset.mem_filter.1 ha1
    have hmem : a \ α ∈ faces (link X α) 1 := by
      refine Finset.mem_filter.2 ⟨?_, ?_⟩
      · exact Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨haX, haα⟩, rfl⟩
      · rw [Finset.card_sdiff_of_subset haα, hac]; omega
    refine ⟨⟨a \ α, hmem⟩, Finset.mem_univ _, ?_⟩
    simp only
    exact Finset.union_sdiff_of_subset haα
  · intro x _; rfl

lemma sum_vertices₂ (α : Finset V) (hα : α ∈ X) (F : Finset V → Finset V → ℝ) :
    ∑ x : faces (link X α) 1, ∑ y : faces (link X α) 1, F (α ∪ x.1) (α ∪ y.1) =
      ∑ a ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a),
        ∑ b ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a), F a b := by
  have h1 : ∀ x : faces (link X α) 1, ∑ y : faces (link X α) 1, F (α ∪ x.1) (α ∪ y.1) =
      ∑ b ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a), F (α ∪ x.1) b :=
    fun x => sum_vertices X α hα (F (α ∪ x.1))
  simp_rw [h1]
  exact sum_vertices X α hα (fun a => ∑ b ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a), F a b)

/-- adjacency weight on flags: faces `a`, `b` with `a ∪ b` a face -/
noncomputable def ADJ (a b : Finset V) : ℝ :=
  if a ≠ b ∧ a ∪ b ∈ X then (fc X d (a ∪ b) : ℝ) else 0

lemma wLinkAdj_entry (α : Finset V) (x y : faces (link X α) 1) :
    wLinkAdj X d α x y = ADJ X d (α ∪ x.1) (α ∪ y.1) := by
  obtain ⟨hx1, hx2, hx3⟩ := link_vertex X α x
  obtain ⟨hy1, hy2, hy3⟩ := link_vertex X α y
  have hu : (α ∪ x.1) ∪ (α ∪ y.1) = α ∪ x.1 ∪ y.1 := by
    ext z; simp only [Finset.mem_union]; tauto
  have hne : x ≠ y ↔ α ∪ x.1 ≠ α ∪ y.1 := by
    constructor
    · intro h h'
      apply h
      apply Subtype.ext
      have h2 : (α ∪ x.1) \ α = (α ∪ y.1) \ α := by rw [h']
      rwa [Finset.union_sdiff_cancel_left hx2, Finset.union_sdiff_cancel_left hy2] at h2
    · intro h h'; exact h (by rw [h'])
  have hlink : x.1 ∪ y.1 ∈ link X α ↔ α ∪ x.1 ∪ y.1 ∈ X := by
    have hd : Disjoint α (x.1 ∪ y.1) := Finset.disjoint_union_right.2 ⟨hx2, hy2⟩
    constructor
    · intro h
      obtain ⟨σ, hσ, hσe⟩ := Finset.mem_image.1 h
      obtain ⟨hσX, hασ⟩ := Finset.mem_filter.1 hσ
      have : σ = α ∪ x.1 ∪ y.1 := by
        rw [Finset.union_assoc, ← hσe, Finset.union_sdiff_of_subset hασ]
      rw [← this]; exact hσX
    · intro h
      refine Finset.mem_image.2 ⟨α ∪ x.1 ∪ y.1, Finset.mem_filter.2 ⟨h, ?_⟩, ?_⟩
      · intro z hz; simp [hz]
      · rw [Finset.union_assoc, Finset.union_sdiff_cancel_left hd]
  unfold wLinkAdj ADJ
  simp only [Matrix.of_apply]
  rw [hu]
  by_cases h : x ≠ y ∧ x.1 ∪ y.1 ∈ link X α
  · rw [if_pos h, if_pos ⟨hne.1 h.1, hlink.1 h.2⟩]
  · rw [if_neg h, if_neg]
    intro h'
    exact h ⟨hne.2 h'.1, hlink.2 h'.2⟩

lemma inter_eq {α a b : Finset V} (hαa : α ⊆ a) (hαb : α ⊆ b) (ha : a.card = α.card + 1)
    (hb : b.card = α.card + 1) (hab : a ≠ b) : a ∩ b = α := by
  have h1 : α ⊆ a ∩ b := Finset.subset_inter hαa hαb
  have h2 : (a ∩ b).card ≤ α.card := by
    by_contra hlt
    have h3 : (a ∩ b).card = a.card := by
      have := Finset.card_le_card h1
      have := Finset.card_le_card (Finset.inter_subset_left : a ∩ b ⊆ a)
      omega
    have h4 : a ∩ b = a := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have h5 : a ⊆ b := h4 ▸ Finset.inter_subset_right
    exact hab (Finset.eq_of_subset_of_card_le h5 (by omega))
  exact (Finset.eq_of_subset_of_card_le h1 h2).symm

lemma sum_adj (hX : IsPure X d) (α : Finset V) {a : Finset V}
    (haT : a ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a)) :
    ∑ b ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a), ADJ X d a b =
      ((d : ℝ) - (α.card + 1 : ℕ)) * (fc X d a : ℝ) := by
  obtain ⟨haS, haα⟩ := Finset.mem_filter.1 haT
  obtain ⟨haX, hac⟩ := Finset.mem_filter.1 haS
  rw [← sum_up X d hX haX (α.card + 1) hac]
  have h0 : ∑ b ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a), ADJ X d a b =
      ∑ b ∈ ((faces X (α.card + 1)).filter (fun a => α ⊆ a)).filter
        (fun b => a ≠ b ∧ a ∪ b ∈ X), (fc X d (a ∪ b) : ℝ) := by
    rw [Finset.sum_filter (p := fun b => a ≠ b ∧ a ∪ b ∈ X)]
    exact Finset.sum_congr rfl fun b _ => rfl
  have h1 : ∑ ρ ∈ faces X (α.card + 1 + 1), (if a ⊆ ρ then (fc X d ρ : ℝ) else 0) =
      ∑ ρ ∈ (faces X (α.card + 1 + 1)).filter (fun ρ => a ⊆ ρ), (fc X d ρ : ℝ) :=
    (Finset.sum_filter _ _).symm
  rw [h0, h1]
  refine Finset.sum_bij (fun b _ => a ∪ b) ?_ ?_ ?_ ?_
  · intro b hb
    obtain ⟨hbT, hne, hab⟩ := Finset.mem_filter.1 hb
    obtain ⟨hbS, hbα⟩ := Finset.mem_filter.1 hbT
    obtain ⟨hbX, hbc⟩ := Finset.mem_filter.1 hbS
    have hi := inter_eq haα hbα hac hbc hne
    have hc := Finset.card_union_add_card_inter a b
    rw [hi] at hc
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hab, ?_⟩, Finset.subset_union_left⟩
    omega
  · intro b hb b' hb' hbb
    obtain ⟨hbT, hne, hab⟩ := Finset.mem_filter.1 hb
    obtain ⟨hbT', hne', hab'⟩ := Finset.mem_filter.1 hb'
    obtain ⟨hbS, hbα⟩ := Finset.mem_filter.1 hbT
    obtain ⟨hbS', hbα'⟩ := Finset.mem_filter.1 hbT'
    have hbc := (Finset.mem_filter.1 hbS).2
    have hbc' := (Finset.mem_filter.1 hbS').2
    have hi := inter_eq haα hbα hac hbc hne
    have hi' := inter_eq haα hbα' hac hbc' hne'
    have key : ∀ c : Finset V, a ∩ c = α → c = ((a ∪ c) \ a) ∪ α := by
      intro c hc
      ext z
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro hz
        by_cases hza : z ∈ a
        · right; rw [← hc]; exact Finset.mem_inter.2 ⟨hza, hz⟩
        · left; exact ⟨Or.inr hz, hza⟩
      · rintro (⟨hz | hz, hza⟩ | hz)
        · exact absurd hz hza
        · exact hz
        · rw [← hc] at hz; exact (Finset.mem_inter.1 hz).2
    rw [key b hi, key b' hi', hbb]
  · intro ρ hρ
    obtain ⟨hρS, haρ⟩ := Finset.mem_filter.1 hρ
    obtain ⟨hρX, hρc⟩ := Finset.mem_filter.1 hρS
    have h1 : (ρ \ a).card = 1 := by
      rw [Finset.card_sdiff_of_subset haρ, hρc, hac]; omega
    obtain ⟨y, hy⟩ := Finset.card_eq_one.1 h1
    have hyρ : y ∈ ρ \ a := by rw [hy]; simp
    rw [Finset.mem_sdiff] at hyρ
    have hyα : y ∉ α := fun h => hyρ.2 (haα h)
    have hbρ : insert y α ⊆ ρ := Finset.insert_subset hyρ.1 (haα.trans haρ)
    have hbX : insert y α ∈ X := hX.1 ρ hρX _ hbρ
    have hbc : (insert y α).card = α.card + 1 := Finset.card_insert_of_notMem hyα
    have hbT : insert y α ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a) :=
      Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hbX, hbc⟩, Finset.subset_insert _ _⟩
    have hne : a ≠ insert y α := by
      intro h; apply hyρ.2; rw [h]; exact Finset.mem_insert_self _ _
    have hun : a ∪ insert y α = ρ := by
      apply Finset.Subset.antisymm
      · exact Finset.union_subset haρ hbρ
      · intro z hz
        by_cases hza : z ∈ a
        · exact Finset.mem_union_left _ hza
        · have : z ∈ ρ \ a := Finset.mem_sdiff.2 ⟨hz, hza⟩
          rw [hy] at this
          have : z = y := by simpa using this
          subst this
          exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    refine ⟨insert y α, Finset.mem_filter.2 ⟨hbT, hne, hun ▸ hρX⟩, hun⟩
  · intro b hb
    rfl

lemma ADJ_symm (a b : Finset V) : ADJ X d a b = ADJ X d b a := by
  unfold ADJ
  rw [Finset.union_comm b a]
  simp only [ne_comm]

lemma fc_mono {a α : Finset V} (h : α ⊆ a) : fc X d a ≤ fc X d α := by
  unfold fc
  exact Finset.card_le_card fun σ hσ =>
    Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hσ).1, h.trans (Finset.mem_filter.1 hσ).2⟩

/-- The local Garland inequality at `α`, in terms of the `j`-faces containing `α`. -/
lemma local_global (hX : IsPure X d) (α : Finset V) (hα : α ∈ X) (hd : α.card + 2 ≤ d)
    (γ : ℝ) (hγ : wLam X d α ≤ γ) (h : Finset V → ℝ) :
    ∑ a ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a),
      ∑ b ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a), ADJ X d a b * h a * h b ≤
    γ * ∑ a ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a),
        ((d : ℝ) - α.card - 1) * (fc X d a : ℝ) * h a ^ 2 +
    (1 - γ) * (∑ a ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a),
        ((d : ℝ) - α.card - 1) * (fc X d a : ℝ) * h a) ^ 2 /
      (((d : ℝ) - α.card - 1) * ((d : ℝ) - α.card) * (fc X d α : ℝ)) := by
  set T := (faces X (α.card + 1)).filter (fun a => α ⊆ a) with hT
  have hdr : (2 : ℝ) ≤ (d : ℝ) - α.card := by
    have : ((α.card + 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast hd
    push_cast at this; linarith
  have hmemT : ∀ x : faces (link X α) 1, α ∪ x.1 ∈ T := by
    intro x
    obtain ⟨h1, h2, h3⟩ := link_vertex X α x
    exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨h1, by
      rw [Finset.card_union_of_disjoint h2, h3]⟩, Finset.subset_union_left⟩
  have hfcα : (1 : ℝ) ≤ fc X d α := fc_pos X d hX hα
  have hdegx : ∀ x : faces (link X α) 1, vdeg (wLinkAdj X d α) x =
      ((d : ℝ) - α.card - 1) * (fc X d (α ∪ x.1) : ℝ) := by
    intro x
    unfold vdeg
    simp_rw [wLinkAdj_entry]
    rw [sum_vertices X α hα (fun b => ADJ X d (α ∪ x.1) b), sum_adj X d hX α (hmemT x)]
    push_cast; ring
  have hsumfc : ∑ a ∈ T, (fc X d a : ℝ) = ((d : ℝ) - α.card) * fc X d α := by
    rw [← sum_up X d hX hα α.card rfl, hT, Finset.sum_filter]
  have hcardT : 2 ≤ T.card := by
    have h1 : ∑ a ∈ T, (fc X d a : ℝ) ≤ T.card * (fc X d α : ℝ) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun a ha => ?_
      have := (Finset.mem_filter.1 ha).2
      exact_mod_cast fc_mono X d this
    rw [hsumfc] at h1
    have h2 : ((d : ℝ) - α.card) ≤ T.card := by
      by_contra hlt
      push Not at hlt
      nlinarith
    have : (2 : ℝ) ≤ T.card := hdr.trans h2
    exact_mod_cast this
  have hcard : 2 ≤ Fintype.card (faces (link X α) 1) := by
    have : Fintype.card (faces (link X α) 1) = T.card := by
      have := sum_vertices X α hα (fun _ => (1 : ℝ))
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
      exact_mod_cast this
    omega
  have hloc := local_ineq (wLinkAdj X d α) hcard
    (fun x y => by rw [wLinkAdj_entry, wLinkAdj_entry, ADJ_symm])
    (fun x y => by
      rw [wLinkAdj_entry]; unfold ADJ; split_ifs
      · exact Nat.cast_nonneg _
      · exact le_rfl)
    (fun x => by
      rw [hdegx x]
      have := fc_pos X d hX (Finset.mem_filter.1 (Finset.mem_filter.1 (hmemT x)).1).1
      have : (0:ℝ) < (d : ℝ) - α.card - 1 := by linarith
      positivity)
    γ hγ (fun x => h (α ∪ x.1))
  have e1 : ∑ x : faces (link X α) 1, ∑ y : faces (link X α) 1,
      wLinkAdj X d α x y * h (α ∪ x.1) * h (α ∪ y.1) =
      ∑ a ∈ T, ∑ b ∈ T, ADJ X d a b * h a * h b := by
    simp_rw [wLinkAdj_entry]
    exact sum_vertices₂ X α hα (fun a b => ADJ X d a b * h a * h b)
  have e2 : ∑ x : faces (link X α) 1, vdeg (wLinkAdj X d α) x * h (α ∪ x.1) ^ 2 =
      ∑ a ∈ T, ((d : ℝ) - α.card - 1) * (fc X d a : ℝ) * h a ^ 2 := by
    simp_rw [hdegx]
    exact sum_vertices X α hα (fun a => ((d : ℝ) - α.card - 1) * (fc X d a : ℝ) * h a ^ 2)
  have e3 : ∑ x : faces (link X α) 1, vdeg (wLinkAdj X d α) x * h (α ∪ x.1) =
      ∑ a ∈ T, ((d : ℝ) - α.card - 1) * (fc X d a : ℝ) * h a := by
    simp_rw [hdegx]
    exact sum_vertices X α hα (fun a => ((d : ℝ) - α.card - 1) * (fc X d a : ℝ) * h a)
  have e4 : ∑ x : faces (link X α) 1, vdeg (wLinkAdj X d α) x =
      ((d : ℝ) - α.card - 1) * ((d : ℝ) - α.card) * (fc X d α : ℝ) := by
    simp_rw [hdegx]
    rw [sum_vertices X α hα (fun a => ((d : ℝ) - α.card - 1) * (fc X d a : ℝ)),
      ← Finset.mul_sum, hsumfc]
    ring
  rw [e1, e2, e3, e4] at hloc
  exact hloc

end link_bridge

section induction

variable (X : Finset (Finset V)) (d : ℕ) {i : ℕ}

/-- weighted squared norm at level `k` -/
noncomputable def Nn (k : ℕ) (h : Finset V → ℝ) : ℝ :=
  ∑ a ∈ faces X k, (fc X d a : ℝ) * h a ^ 2

/-- `⟨h, P^∨ h⟩` at level `i+1`, written through the faces of level `i` -/
noncomputable def Qq (i : ℕ) (h : Finset V → ℝ) : ℝ :=
  (1 / (((i : ℝ) + 1) * ((d : ℝ) - i))) * ∑ α ∈ faces X i, (1 / (fc X d α : ℝ)) *
    (∑ a ∈ faces X (i + 1), if α ⊆ a then (fc X d a : ℝ) * h a else 0) ^ 2

/-- the down-averaged function -/
noncomputable def mm (i : ℕ) (f : Finset V → ℝ) (c : Finset V) : ℝ :=
  ∑ a ∈ faces X (i + 2), if c ⊆ a then (fc X d a : ℝ) * f a else 0

noncomputable def hh (i : ℕ) (f : Finset V → ℝ) (c : Finset V) : ℝ :=
  mm X d i f c / (((d : ℝ) - (i + 1)) * (fc X d c : ℝ))

lemma sum_down_const (hX : IsPure X d) {a : Finset V} (ha : a ∈ X) (k : ℕ) (hak : a.card = k + 1)
    (F : ℝ) : ∑ c ∈ faces X k, (if c ⊆ a then F else 0) = ((k : ℝ) + 1) * F := by
  rw [← Finset.sum_filter, Finset.sum_const, card_sub X d hX ha, hak, nsmul_eq_mul,
    Nat.choose_succ_self_right]
  push_cast; ring

lemma mm_eq (hX : IsPure X d) (hd : i + 2 ≤ d) (f : Finset V → ℝ) {c : Finset V}
    (hc : c ∈ faces X (i + 1)) :
    mm X d i f c = ((d : ℝ) - (i + 1)) * (fc X d c : ℝ) * hh X d i f c := by
  have h1 := fc_pos X d hX (Finset.mem_filter.1 hc).1
  have hdr : (1 : ℝ) ≤ (d : ℝ) - (i + 1) := by
    have : ((i + 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast hd
    push_cast at this; linarith
  unfold hh
  field_simp

lemma mean_h (hX : IsPure X d) (hd : i + 2 ≤ d) (f : Finset V → ℝ)
    (hf : ∑ a ∈ faces X (i + 2), (fc X d a : ℝ) * f a = 0) :
    ∑ c ∈ faces X (i + 1), (fc X d c : ℝ) * hh X d i f c = 0 := by
  have hdr : (1 : ℝ) ≤ (d : ℝ) - (i + 1) := by
    have : ((i + 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast hd
    push_cast at this; linarith
  have h1 : ∑ c ∈ faces X (i + 1), mm X d i f c = 0 := by
    unfold mm
    rw [Finset.sum_comm]
    have : ∀ a ∈ faces X (i + 2), ∑ c ∈ faces X (i + 1),
        (if c ⊆ a then (fc X d a : ℝ) * f a else 0) = (((i + 1 : ℕ) : ℝ) + 1) * ((fc X d a : ℝ) * f a) := by
      intro a ha
      obtain ⟨haX, hac⟩ := Finset.mem_filter.1 ha
      exact sum_down_const X d hX haX (i + 1) hac _
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hf, mul_zero]
  have h2 : ∀ c ∈ faces X (i + 1), (fc X d c : ℝ) * hh X d i f c =
      mm X d i f c / ((d : ℝ) - (i + 1)) := by
    intro c hc
    rw [mm_eq X d hX hd f hc]
    have := fc_pos X d hX (Finset.mem_filter.1 hc).1
    field_simp
  rw [Finset.sum_congr rfl h2, ← Finset.sum_div, h1, zero_div]

noncomputable def uu (i : ℕ) (h : Finset V → ℝ) (a : Finset V) : ℝ :=
  (1 / ((i : ℝ) + 2)) * ∑ c ∈ faces X (i + 1), if c ⊆ a then h c else 0

/-- adjacency weight of two `(i+1)`-faces spanning an `(i+2)`-face -/
noncomputable def ADJ' (i : ℕ) (c c' : Finset V) : ℝ :=
  if c ≠ c' ∧ c ∪ c' ∈ faces X (i + 2) then (fc X d (c ∪ c') : ℝ) else 0

noncomputable def Cr (i : ℕ) (h : Finset V → ℝ) : ℝ :=
  ∑ c ∈ faces X (i + 1), ∑ c' ∈ faces X (i + 1), ADJ' X d i c c' * h c * h c'

lemma Qq_succ (hX : IsPure X d) (hd : i + 2 ≤ d) (f : Finset V → ℝ) :
    Qq X d (i + 1) f = (((d : ℝ) - (i + 1)) / ((i : ℝ) + 2)) * Nn X d (i + 1) (hh X d i f) := by
  have hdr : (1 : ℝ) ≤ (d : ℝ) - (i + 1) := by
    have : ((i + 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast hd
    push_cast at this; linarith
  unfold Qq Nn
  have h1 : ∀ α ∈ faces X (i + 1), (1 / (fc X d α : ℝ)) *
      (∑ a ∈ faces X (i + 1 + 1), if α ⊆ a then (fc X d a : ℝ) * f a else 0) ^ 2 =
      ((d : ℝ) - (i + 1)) ^ 2 * ((fc X d α : ℝ) * hh X d i f α ^ 2) := by
    intro α hα
    have := mm_eq X d hX hd f hα
    have hp := fc_pos X d hX (Finset.mem_filter.1 hα).1
    change (1 / (fc X d α : ℝ)) * mm X d i f α ^ 2 = _
    rw [this]
    field_simp
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  push_cast
  field_simp
  ring

lemma inner_eq (hX : IsPure X d) (hd : i + 2 ≤ d) (f : Finset V → ℝ) :
    ∑ a ∈ faces X (i + 2), (fc X d a : ℝ) * f a * uu X i (hh X d i f) a =
      (((d : ℝ) - (i + 1)) / ((i : ℝ) + 2)) * Nn X d (i + 1) (hh X d i f) := by
  unfold uu Nn
  have h1 : ∀ a ∈ faces X (i + 2), (fc X d a : ℝ) * f a * ((1 / ((i : ℝ) + 2)) *
      ∑ c ∈ faces X (i + 1), if c ⊆ a then hh X d i f c else 0) =
      (1 / ((i : ℝ) + 2)) * ∑ c ∈ faces X (i + 1),
        (if c ⊆ a then (fc X d a : ℝ) * f a * hh X d i f c else 0) := by
    intro a _
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs <;> ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_comm]
  have h2 : ∀ c ∈ faces X (i + 1), ∑ a ∈ faces X (i + 2),
      (if c ⊆ a then (fc X d a : ℝ) * f a * hh X d i f c else 0) =
      ((d : ℝ) - (i + 1)) * ((fc X d c : ℝ) * hh X d i f c ^ 2) := by
    intro c hc
    have : ∑ a ∈ faces X (i + 2),
        (if c ⊆ a then (fc X d a : ℝ) * f a * hh X d i f c else 0) =
        mm X d i f c * hh X d i f c := by
      unfold mm
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by split_ifs <;> ring
    rw [this, mm_eq X d hX hd f hc]; ring
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
  field_simp

lemma pair_sum (hX : IsPure X d) {c c' : Finset V} (hc : c ∈ faces X (i + 1))
    (hc' : c' ∈ faces X (i + 1)) :
    ∑ a ∈ faces X (i + 2), (if c ⊆ a ∧ c' ⊆ a then (fc X d a : ℝ) else 0) =
      (if c = c' then ((d : ℝ) - (i + 1)) * (fc X d c : ℝ) else 0) + ADJ' X d i c c' := by
  obtain ⟨hcX, hcc⟩ := Finset.mem_filter.1 hc
  obtain ⟨hcX', hcc'⟩ := Finset.mem_filter.1 hc'
  by_cases hcc'e : c = c'
  · subst hcc'e
    have : ADJ' X d i c c = 0 := by simp [ADJ']
    rw [this, add_zero, if_pos rfl]
    have h := sum_up X d hX hcX (i + 1) hcc
    push_cast at h
    rw [← h]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp
  · rw [if_neg hcc'e, zero_add]
    have hlt : c.card < (c ∪ c').card := by
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_union_left, fun h => hcc'e ?_⟩
      have h2 : c' ⊆ c := h ▸ Finset.subset_union_right
      exact (Finset.eq_of_subset_of_card_le h2 (by omega)).symm
    by_cases hu : c ∪ c' ∈ faces X (i + 2)
    · rw [Finset.sum_eq_single (c ∪ c')]
      · simp [ADJ', hcc'e, hu, Finset.subset_union_left, Finset.subset_union_right]
      · intro a ha hne
        rw [if_neg]
        rintro ⟨h1, h2⟩
        have h3 : c ∪ c' ⊆ a := Finset.union_subset h1 h2
        have hac := (Finset.mem_filter.1 ha).2
        have huc := (Finset.mem_filter.1 hu).2
        exact hne (Finset.eq_of_subset_of_card_le h3 (by omega)).symm
      · intro h; exact absurd hu h
    · rw [Finset.sum_eq_zero]
      · simp [ADJ', hu]
      · intro a ha
        rw [if_neg]
        rintro ⟨h1, h2⟩
        have h3 : c ∪ c' ⊆ a := Finset.union_subset h1 h2
        have hac := (Finset.mem_filter.1 ha).2
        have heq : c ∪ c' = a := Finset.eq_of_subset_of_card_le h3 (by omega)
        exact hu (heq ▸ ha)

lemma garland_G1 (hX : IsPure X d) (h : Finset V → ℝ) :
    ∑ a ∈ faces X (i + 2), (fc X d a : ℝ) *
        (∑ c ∈ faces X (i + 1), if c ⊆ a then h c else 0) ^ 2 =
      ((d : ℝ) - (i + 1)) * Nn X d (i + 1) h + Cr X d i h := by
  have h1 : ∀ a ∈ faces X (i + 2), (fc X d a : ℝ) *
        (∑ c ∈ faces X (i + 1), if c ⊆ a then h c else 0) ^ 2 =
      ∑ c ∈ faces X (i + 1), ∑ c' ∈ faces X (i + 1),
        (if c ⊆ a ∧ c' ⊆ a then (fc X d a : ℝ) else 0) * (h c * h c') := by
    intro a _
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    by_cases h1 : c ⊆ a <;> by_cases h2 : c' ⊆ a <;> simp [h1, h2]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∀ c ∈ faces X (i + 1), ∑ a ∈ faces X (i + 2), ∑ c' ∈ faces X (i + 1),
        (if c ⊆ a ∧ c' ⊆ a then (fc X d a : ℝ) else 0) * (h c * h c') =
      ((d : ℝ) - (i + 1)) * ((fc X d c : ℝ) * h c ^ 2) +
        ∑ c' ∈ faces X (i + 1), ADJ' X d i c c' * h c * h c' := by
    intro c hc
    rw [Finset.sum_comm]
    have h3 : ∀ c' ∈ faces X (i + 1), ∑ a ∈ faces X (i + 2),
        (if c ⊆ a ∧ c' ⊆ a then (fc X d a : ℝ) else 0) * (h c * h c') =
        (if c = c' then ((d : ℝ) - (i + 1)) * (fc X d c : ℝ) * h c ^ 2 else 0) +
          ADJ' X d i c c' * h c * h c' := by
      intro c' hc'
      rw [← Finset.sum_mul, pair_sum X d hX hc hc']
      split_ifs with he
      · subst he; ring
      · ring
    rw [Finset.sum_congr rfl h3, Finset.sum_add_distrib, Finset.sum_ite_eq]
    rw [if_pos hc]
    ring
  rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, Cr, Nn, Finset.mul_sum]

lemma alpha_pair (hX : IsPure X d) {a b : Finset V} (ha : a ∈ faces X (i + 1))
    (hb : b ∈ faces X (i + 1)) :
    ∑ α ∈ faces X i, (if α ⊆ a ∧ α ⊆ b then ADJ X d a b else 0) = ADJ' X d i a b := by
  obtain ⟨haX, hac⟩ := Finset.mem_filter.1 ha
  obtain ⟨hbX, hbc⟩ := Finset.mem_filter.1 hb
  by_cases hab : a = b
  · subst hab
    simp [ADJ, ADJ']
  by_cases hu : a ∪ b ∈ faces X (i + 2)
  · obtain ⟨huX, huc⟩ := Finset.mem_filter.1 hu
    have hcu := Finset.card_union_add_card_inter a b
    have hic : (a ∩ b).card = i := by omega
    have hiX : a ∩ b ∈ faces X i :=
      Finset.mem_filter.2 ⟨hX.1 a haX _ Finset.inter_subset_left, hic⟩
    rw [Finset.sum_eq_single (a ∩ b)]
    · simp [ADJ, ADJ', hab, huX, hu]
    · intro α hα hne
      rw [if_neg]
      rintro ⟨h1, h2⟩
      apply hne
      have hα' := (Finset.mem_filter.1 hα).2
      exact (Finset.eq_of_subset_of_card_le (Finset.subset_inter h1 h2) (by omega))
    · intro h; exact absurd hiX h
  · have : ADJ' X d i a b = 0 := by simp [ADJ', hu]
    rw [this]
    refine Finset.sum_eq_zero fun α hα => ?_
    by_cases hc : α ⊆ a ∧ α ⊆ b
    · rw [if_pos hc]
      have hα' := (Finset.mem_filter.1 hα).2
      have hi := inter_eq hc.1 hc.2 (by omega) (by omega) hab
      have hcu := Finset.card_union_add_card_inter a b
      rw [hi] at hcu
      have hnX : a ∪ b ∉ X := fun hm => hu (Finset.mem_filter.2 ⟨hm, by omega⟩)
      simp [ADJ, hnX]
    · rw [if_neg hc]

lemma alpha_decomp (hX : IsPure X d) (h : Finset V → ℝ) :
    ∑ α ∈ faces X i, ∑ a ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a),
        ∑ b ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a), ADJ X d a b * h a * h b =
      Cr X d i h := by
  have h1 : ∀ α ∈ faces X i, ∑ a ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a),
        ∑ b ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a), ADJ X d a b * h a * h b =
      ∑ a ∈ faces X (i + 1), ∑ b ∈ faces X (i + 1),
        (if α ⊆ a ∧ α ⊆ b then ADJ X d a b else 0) * h a * h b := by
    intro α hα
    have hc : α.card = i := (Finset.mem_filter.1 hα).2
    rw [hc, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_filter]
    by_cases h1 : α ⊆ a
    · rw [if_pos h1]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases h2 : α ⊆ b <;> simp [h1, h2]
    · simp [h1]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  unfold Cr
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul, alpha_pair X d hX ha hb]

lemma Cr_le (hX : IsPure X d) (hd : i + 2 ≤ d) (γ : ℝ)
    (hγ : ∀ α ∈ faces X i, wLam X d α ≤ γ) (h : Finset V → ℝ) :
    Cr X d i h ≤ γ * (((d : ℝ) - (i + 1)) * ((i : ℝ) + 1) * Nn X d (i + 1) h) +
      (1 - γ) * (((d : ℝ) - (i + 1)) * ((i : ℝ) + 1) * Qq X d i h) := by
  have hdr : (1 : ℝ) ≤ (d : ℝ) - (i + 1) := by
    have : ((i + 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast hd
    push_cast at this; linarith
  have h1 : Cr X d i h ≤ ∑ α ∈ faces X i,
      (γ * ∑ a ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a),
          ((d : ℝ) - α.card - 1) * (fc X d a : ℝ) * h a ^ 2 +
        (1 - γ) * (∑ a ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a),
          ((d : ℝ) - α.card - 1) * (fc X d a : ℝ) * h a) ^ 2 /
        (((d : ℝ) - α.card - 1) * ((d : ℝ) - α.card) * (fc X d α : ℝ))) := by
    rw [← alpha_decomp X d hX h]
    refine Finset.sum_le_sum fun α hα => ?_
    obtain ⟨hαX, hc⟩ := Finset.mem_filter.1 hα
    exact local_global X d hX α hαX (by omega) γ (hγ α hα) h
  refine h1.trans (le_of_eq ?_)
  have h2 : ∀ α ∈ faces X i,
      (γ * ∑ a ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a),
          ((d : ℝ) - α.card - 1) * (fc X d a : ℝ) * h a ^ 2 +
        (1 - γ) * (∑ a ∈ (faces X (α.card + 1)).filter (fun a => α ⊆ a),
          ((d : ℝ) - α.card - 1) * (fc X d a : ℝ) * h a) ^ 2 /
        (((d : ℝ) - α.card - 1) * ((d : ℝ) - α.card) * (fc X d α : ℝ))) =
      γ * (((d : ℝ) - (i + 1)) * ∑ a ∈ faces X (i + 1),
          (if α ⊆ a then (fc X d a : ℝ) * h a ^ 2 else 0)) +
      (1 - γ) * (((d : ℝ) - (i + 1)) / ((d : ℝ) - i)) * ((1 / (fc X d α : ℝ)) *
        (∑ a ∈ faces X (i + 1), if α ⊆ a then (fc X d a : ℝ) * h a else 0) ^ 2) := by
    intro α hα
    obtain ⟨hαX, hc⟩ := Finset.mem_filter.1 hα
    have hp := fc_pos X d hX hαX
    rw [hc, Finset.sum_filter, Finset.sum_filter]
    have e1 : ∑ a ∈ faces X (i + 1), (if α ⊆ a then
        ((d : ℝ) - i - 1) * (fc X d a : ℝ) * h a ^ 2 else 0) =
        ((d : ℝ) - (i + 1)) * ∑ a ∈ faces X (i + 1),
          (if α ⊆ a then (fc X d a : ℝ) * h a ^ 2 else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> ring
    have e2 : ∑ a ∈ faces X (i + 1), (if α ⊆ a then
        ((d : ℝ) - i - 1) * (fc X d a : ℝ) * h a else 0) =
        ((d : ℝ) - (i + 1)) * ∑ a ∈ faces X (i + 1),
          (if α ⊆ a then (fc X d a : ℝ) * h a else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> ring
    rw [e1, e2]
    have hdi : (0 : ℝ) < (d : ℝ) - i := by linarith
    have : (0 : ℝ) < (d : ℝ) - (i + 1) := by linarith
    have e3 : (d : ℝ) - i - 1 = (d : ℝ) - (i + 1) := by ring
    rw [e3]
    field_simp
  rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  · congr 1
    rw [Finset.sum_comm]
    have : ∀ a ∈ faces X (i + 1), ∑ α ∈ faces X i, (if α ⊆ a then (fc X d a : ℝ) * h a ^ 2 else 0) =
        ((i : ℝ) + 1) * ((fc X d a : ℝ) * h a ^ 2) := by
      intro a ha
      obtain ⟨haX, hac⟩ := Finset.mem_filter.1 ha
      exact sum_down_const X d hX haX i hac _
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    unfold Nn
    ring
  · have hdi : (0 : ℝ) < (d : ℝ) - i := by linarith
    unfold Qq
    rw [← Finset.mul_sum]
    generalize (∑ α ∈ faces X i, (1 / (fc X d α : ℝ)) *
      (∑ a ∈ faces X (i + 1), if α ⊆ a then (fc X d a : ℝ) * h a else 0) ^ 2) = S
    field_simp

lemma wcs {ι : Type*} (s : Finset ι) (w x y : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i ∈ s, w i * x i * y i) ^ 2 ≤ (∑ i ∈ s, w i * x i ^ 2) * ∑ i ∈ s, w i * y i ^ 2 := by
  have := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (w i) * x i)
    (fun i => Real.sqrt (w i) * y i)
  have e : ∀ i, Real.sqrt (w i) * Real.sqrt (w i) = w i := fun i => Real.mul_self_sqrt (hw i)
  have e1 : ∀ i, Real.sqrt (w i) * x i * (Real.sqrt (w i) * y i) = w i * x i * y i := by
    intro i
    calc Real.sqrt (w i) * x i * (Real.sqrt (w i) * y i) =
        (Real.sqrt (w i) * Real.sqrt (w i)) * x i * y i := by ring
      _ = w i * x i * y i := by rw [e i]
  have e2 : ∀ i, (Real.sqrt (w i) * x i) ^ 2 = w i * x i ^ 2 := by
    intro i; rw [mul_pow, Real.sq_sqrt (hw i)]
  have e3 : ∀ i, (Real.sqrt (w i) * y i) ^ 2 = w i * y i ^ 2 := by
    intro i; rw [mul_pow, Real.sq_sqrt (hw i)]
  simpa only [e1, e2, e3] using this

/-- the Alev–Lau constant at level `i+1` -/
noncomputable def kap (γ : ℕ → ℝ) (i : ℕ) : ℝ :=
  (1 / ((i : ℝ) + 1)) * ∏ m ∈ Finset.range i, (1 - γ m)

lemma kap_succ (γ : ℕ → ℝ) (i : ℕ) :
    kap γ (i + 1) = (((i : ℝ) + 1) / ((i : ℝ) + 2)) * (1 - γ i) * kap γ i := by
  unfold kap
  rw [Finset.prod_range_succ]
  push_cast
  have h1 : (i : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (i : ℝ) + 1 + 1 ≠ 0 := by positivity
  have h3 : (i : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

lemma kap_nonneg (γ : ℕ → ℝ) (h1 : ∀ m, γ m ≤ 1) (i : ℕ) : 0 ≤ kap γ i := by
  unfold kap
  exact mul_nonneg (by positivity) (Finset.prod_nonneg fun m _ => by linarith [h1 m])

lemma kap_le_one (γ : ℕ → ℝ) (h0 : ∀ m, 0 ≤ γ m) (h1 : ∀ m, γ m ≤ 1) (i : ℕ) : kap γ i ≤ 1 := by
  unfold kap
  have hp : ∏ m ∈ Finset.range i, (1 - γ m) ≤ 1 :=
    Finset.prod_le_one (fun m _ => by linarith [h1 m]) (fun m _ => by linarith [h0 m])
  have hp0 : 0 ≤ ∏ m ∈ Finset.range i, (1 - γ m) :=
    Finset.prod_nonneg fun m _ => by linarith [h1 m]
  have : 1 / ((i : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith
  calc _ ≤ 1 * 1 := mul_le_mul this hp hp0 (by norm_num)
    _ = 1 := by norm_num

lemma step (hX : IsPure X d) (hd : i + 2 ≤ d) (γ κ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hγi : ∀ α ∈ faces X i, wLam X d α ≤ γ)
    (IH : ∀ h : Finset V → ℝ, ∑ a ∈ faces X (i + 1), (fc X d a : ℝ) * h a = 0 →
      Qq X d i h ≤ (1 - κ) * Nn X d (i + 1) h)
    (f : Finset V → ℝ) (hf : ∑ a ∈ faces X (i + 2), (fc X d a : ℝ) * f a = 0) :
    Qq X d (i + 1) f ≤
      (1 - (((i : ℝ) + 1) / ((i : ℝ) + 2)) * (1 - γ) * κ) * Nn X d (i + 2) f := by
  have hdr : (1 : ℝ) ≤ (d : ℝ) - (i + 1) := by
    have : ((i + 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast hd
    push_cast at this; linarith
  set h := hh X d i f with hh_def
  set e : ℝ := (d : ℝ) - (i + 1) with he
  set N := Nn X d (i + 1) h with hN
  set Nf := Nn X d (i + 2) f with hNf
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun a ha => by
    have := fc_pos X d hX (Finset.mem_filter.1 ha).1
    positivity
  have hNf0 : 0 ≤ Nf := Finset.sum_nonneg fun a ha => by
    have := fc_pos X d hX (Finset.mem_filter.1 ha).1
    positivity
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hIH := IH h (mean_h X d hX hd f hf)
  have hCr := Cr_le X d hX hd γ hγi h
  have hG := garland_G1 X d (i := i) hX h
  have hT : Qq X d (i + 1) f = (e / ((i : ℝ) + 2)) * N := Qq_succ X d hX hd f
  have hTin := inner_eq X d hX hd f
  -- U2
  have hU2 : ∑ a ∈ faces X (i + 2), (fc X d a : ℝ) * uu X i h a ^ 2 =
      (1 / ((i : ℝ) + 2) ^ 2) * (e * N + Cr X d i h) := by
    rw [← hG, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    unfold uu
    field_simp
  have hCS := wcs (faces X (i + 2)) (fun a => (fc X d a : ℝ)) f (uu X i h)
    (fun a => by positivity)
  rw [hTin, hU2] at hCS
  -- bound on Cr
  have hCr2 : Cr X d i h ≤ e * ((i : ℝ) + 1) * N * (1 - (1 - γ) * κ) := by
    have h1 : (1 - γ) * (e * ((i : ℝ) + 1) * Qq X d i h) ≤
        (1 - γ) * (e * ((i : ℝ) + 1) * ((1 - κ) * N)) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact mul_le_mul_of_nonneg_left hIH (by positivity)
    nlinarith
  rw [hT]
  set T := (e / ((i : ℝ) + 2)) * N with hTdef
  have hT0 : 0 ≤ T := by positivity
  have hi2 : (0 : ℝ) < (i : ℝ) + 2 := by positivity
  set κ' : ℝ := (((i : ℝ) + 1) / ((i : ℝ) + 2)) * (1 - γ) * κ with hκ'
  have hκ'1 : κ' ≤ 1 := by
    have : ((i : ℝ) + 1) / ((i : ℝ) + 2) ≤ 1 := by rw [div_le_one hi2]; linarith
    have h2 : (1 - γ) * κ ≤ 1 := by nlinarith
    have h3 : 0 ≤ (1 - γ) * κ := by nlinarith
    calc κ' = (((i : ℝ) + 1) / ((i : ℝ) + 2)) * ((1 - γ) * κ) := by rw [hκ']; ring
      _ ≤ 1 * 1 := mul_le_mul this h2 h3 (by norm_num)
      _ = 1 := by norm_num
  have hU : (1 / ((i : ℝ) + 2) ^ 2) * (e * N + Cr X d i h) ≤ T * (1 - κ') := by
    have : e * N + Cr X d i h ≤ e * N * ((i : ℝ) + 2) * (1 - κ') := by
      rw [hκ']
      have : e * N * ((i : ℝ) + 2) * (1 - ((i + 1) / (i + 2)) * (1 - γ) * κ) =
          e * N * ((i : ℝ) + 2) - e * N * ((i : ℝ) + 1) * ((1 - γ) * κ) := by
        field_simp
      rw [this]
      have h' : e * N * ((i : ℝ) + 2) - e * N * ((i : ℝ) + 1) * ((1 - γ) * κ) =
          e * N + e * ((i : ℝ) + 1) * N * (1 - (1 - γ) * κ) := by ring
      rw [h']; linarith
    calc (1 / ((i : ℝ) + 2) ^ 2) * (e * N + Cr X d i h)
        ≤ (1 / ((i : ℝ) + 2) ^ 2) * (e * N * ((i : ℝ) + 2) * (1 - κ')) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = T * (1 - κ') := by rw [hTdef]; field_simp
  have h5 : T ^ 2 ≤ Nf * (T * (1 - κ')) :=
    hCS.trans (mul_le_mul_of_nonneg_left hU hNf0)
  rcases hT0.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg (sub_nonneg.2 hκ'1) hNf0
  · have h6 : T * T ≤ T * (Nf * (1 - κ')) :=
      calc T * T = T ^ 2 := (sq T).symm
        _ ≤ Nf * (T * (1 - κ')) := h5
        _ = T * (Nf * (1 - κ')) := by ring
    have h7 := le_of_mul_le_mul_left h6 hpos
    exact h7.trans (le_of_eq (mul_comm _ _))

lemma rayleigh_levels (hX : IsPure X d) (γ : ℕ → ℝ) (h0 : ∀ m, 0 ≤ γ m) (h1 : ∀ m, γ m ≤ 1)
    (J : ℕ) (hJ : J ≤ d)
    (hγ : ∀ α ∈ X, α.card + 2 ≤ J → wLam X d α ≤ γ α.card) :
    ∀ i : ℕ, i + 1 ≤ J → ∀ h : Finset V → ℝ,
      ∑ a ∈ faces X (i + 1), (fc X d a : ℝ) * h a = 0 →
      Qq X d i h ≤ (1 - kap γ i) * Nn X d (i + 1) h := by
  intro i
  induction i with
  | zero =>
    intro _ h hh
    have : Qq X d 0 h = 0 := by
      unfold Qq
      have : ∀ α ∈ faces X 0, (1 / (fc X d α : ℝ)) *
          (∑ a ∈ faces X (0 + 1), if α ⊆ a then (fc X d a : ℝ) * h a else 0) ^ 2 = 0 := by
        intro α hα
        have hc := (Finset.mem_filter.1 hα).2
        have : α = ∅ := Finset.card_eq_zero.1 hc
        subst this
        simp only [Finset.empty_subset, if_true]
        rw [hh]; simp
      rw [Finset.sum_eq_zero this, mul_zero]
    rw [this]
    have : kap γ 0 = 1 := by simp [kap]
    rw [this]; simp
  | succ i ih =>
    intro hi f hf
    have hd : i + 2 ≤ d := by omega
    have := step X d (i := i) hX hd (γ i) (kap γ i) (h0 i) (h1 i) (kap_nonneg γ h1 i)
      (kap_le_one γ h0 h1 i)
      (fun α hα => by
        obtain ⟨hαX, hc⟩ := Finset.mem_filter.1 hα
        have := hγ α hαX (by omega)
        rwa [hc] at this)
      (ih (by omega)) f hf
    rw [kap_succ]
    exact this

lemma erase_sum (hX : IsPure X d) {a : Finset V} (ha : a ∈ faces X (i + 1)) (G : Finset V → ℝ) :
    ∑ v ∈ a, G (a.erase v) = ∑ c ∈ faces X i, (if c ⊆ a then G c else 0) := by
  obtain ⟨haX, hac⟩ := Finset.mem_filter.1 ha
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun v _ => a.erase v) ?_ ?_ ?_ ?_
  · intro v hv
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hX.1 a haX _ (Finset.erase_subset _ _), ?_⟩,
      Finset.erase_subset _ _⟩
    rw [Finset.card_erase_of_mem hv, hac]; rfl
  · intro v hv w hw hvw
    by_contra hne
    have : w ∈ a.erase v := Finset.mem_erase.2 ⟨Ne.symm hne, hw⟩
    rw [hvw] at this
    exact (Finset.notMem_erase w a) this
  · intro c hc
    obtain ⟨hc1, hca⟩ := Finset.mem_filter.1 hc
    obtain ⟨hcX, hcc⟩ := Finset.mem_filter.1 hc1
    have h1 : (a \ c).card = 1 := by
      rw [Finset.card_sdiff_of_subset hca, hac, hcc]; omega
    obtain ⟨v, hv⟩ := Finset.card_eq_one.1 h1
    have hva : v ∈ a \ c := by rw [hv]; simp
    rw [Finset.mem_sdiff] at hva
    refine ⟨v, hva.1, ?_⟩
    ext z
    simp only [Finset.mem_erase]
    constructor
    · rintro ⟨hzv, hza⟩
      by_contra hzc
      have : z ∈ a \ c := Finset.mem_sdiff.2 ⟨hza, hzc⟩
      rw [hv] at this
      exact hzv (by simpa using this)
    · intro hz
      refine ⟨?_, hca hz⟩
      rintro rfl
      exact hva.2 hz
  · intro v _; rfl

lemma W_cform (hX : IsPure X d) (hi : i + 1 ≤ d) (a b : faces X (i + 1)) :
    wDownUp X d (i + 1) a b = (1 / (((i : ℝ) + 1) * ((d : ℝ) - i))) *
      ∑ c ∈ faces X i, (if c ⊆ a.1 ∧ c ⊆ b.1 then (fc X d b.1 : ℝ) / (fc X d c : ℝ) else 0) := by
  have hdi : (0 : ℝ) < (d : ℝ) - i := by
    have : ((i + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hi
    push_cast at this; linarith
  unfold wDownUp
  simp only [Matrix.of_apply]
  have hden : ∀ v ∈ a.1, ∑ ρ ∈ (faces X (i + 1)).filter (fun ρ => a.1.erase v ⊆ ρ),
      (fc X d ρ : ℝ) = ((d : ℝ) - i) * (fc X d (a.1.erase v) : ℝ) := by
    intro v hv
    obtain ⟨haX, hac⟩ := Finset.mem_filter.1 a.2
    have hcX : a.1.erase v ∈ X := hX.1 a.1 haX _ (Finset.erase_subset _ _)
    have hcc : (a.1.erase v).card = i := by
      rw [Finset.card_erase_of_mem hv, hac]; rfl
    rw [← sum_up X d hX hcX i hcc, Finset.sum_filter]
  have h1 : ∑ v ∈ a.1, (if a.1.erase v ⊆ b.1 then (fc X d b.1 : ℝ) /
      ∑ ρ ∈ (faces X (i + 1)).filter (fun ρ => a.1.erase v ⊆ ρ), (fc X d ρ : ℝ) else 0) =
      ∑ v ∈ a.1, (if a.1.erase v ⊆ b.1 then (fc X d b.1 : ℝ) /
        (((d : ℝ) - i) * (fc X d (a.1.erase v) : ℝ)) else 0) := by
    refine Finset.sum_congr rfl fun v hv => ?_
    simp only [hden v hv]
  rw [h1, erase_sum X d hX a.2 (fun c => if c ⊆ b.1 then (fc X d b.1 : ℝ) /
        (((d : ℝ) - i) * (fc X d c : ℝ)) else 0), Finset.mul_sum, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun c hc => ?_
  have hp := fc_pos X d hX (Finset.mem_filter.1 hc).1
  by_cases h1 : c ⊆ a.1 <;> by_cases h2 : c ⊆ b.1 <;> simp [h1, h2]
  field_simp

/-- the symmetric weight matrix `fc a * wDownUp a b` -/
noncomputable def Wf (i : ℕ) : Matrix (faces X (i + 1)) (faces X (i + 1)) ℝ :=
  Matrix.of fun a b => (fc X d a.1 : ℝ) * wDownUp X d (i + 1) a b

lemma Wf_cform (hX : IsPure X d) (hi : i + 1 ≤ d) (a b : faces X (i + 1)) :
    Wf X d i a b = (1 / (((i : ℝ) + 1) * ((d : ℝ) - i))) *
      ∑ c ∈ faces X i, (if c ⊆ a.1 ∧ c ⊆ b.1 then
        (fc X d a.1 : ℝ) * (fc X d b.1 : ℝ) / (fc X d c : ℝ) else 0) := by
  unfold Wf
  simp only [Matrix.of_apply]
  rw [W_cform X d hX hi, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> ring

lemma Wf_symm (hX : IsPure X d) (hi : i + 1 ≤ d) (a b : faces X (i + 1)) :
    Wf X d i a b = Wf X d i b a := by
  rw [Wf_cform X d hX hi, Wf_cform X d hX hi]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h1 : c ⊆ a.1 <;> by_cases h2 : c ⊆ b.1 <;> simp [h1, h2, mul_comm]

lemma Wf_nonneg (hX : IsPure X d) (hi : i + 1 ≤ d) (a b : faces X (i + 1)) :
    0 ≤ Wf X d i a b := by
  rw [Wf_cform X d hX hi]
  have hdi : (0 : ℝ) < (d : ℝ) - i := by
    have : ((i + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hi
    push_cast at this; linarith
  apply mul_nonneg (by positivity)
  refine Finset.sum_nonneg fun c hc => ?_
  have hp := fc_pos X d hX (Finset.mem_filter.1 hc).1
  have ha := fc_pos X d hX (Finset.mem_filter.1 a.2).1
  have hb := fc_pos X d hX (Finset.mem_filter.1 b.2).1
  split_ifs
  · positivity
  · exact le_rfl

lemma W_rowsum (hX : IsPure X d) (hi : i + 1 ≤ d) (a : faces X (i + 1)) :
    ∑ b : faces X (i + 1), wDownUp X d (i + 1) a b = 1 := by
  have hdi : (0 : ℝ) < (d : ℝ) - i := by
    have : ((i + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hi
    push_cast at this; linarith
  simp_rw [W_cform X d hX hi]
  rw [← Finset.mul_sum]
  have h1 : ∑ b : faces X (i + 1), ∑ c ∈ faces X i,
      (if c ⊆ a.1 ∧ c ⊆ b.1 then (fc X d b.1 : ℝ) / (fc X d c : ℝ) else 0) =
      ∑ b ∈ faces X (i + 1), ∑ c ∈ faces X i,
      (if c ⊆ a.1 ∧ c ⊆ b then (fc X d b : ℝ) / (fc X d c : ℝ) else 0) :=
    Finset.sum_coe_sort (faces X (i + 1)) (fun b => ∑ c ∈ faces X i,
      (if c ⊆ a.1 ∧ c ⊆ b then (fc X d b : ℝ) / (fc X d c : ℝ) else 0))
  rw [h1, Finset.sum_comm]
  obtain ⟨haX, hac⟩ := Finset.mem_filter.1 a.2
  have h2 : ∀ c ∈ faces X i, ∑ b ∈ faces X (i + 1),
      (if c ⊆ a.1 ∧ c ⊆ b then (fc X d b : ℝ) / (fc X d c : ℝ) else 0) =
      if c ⊆ a.1 then ((d : ℝ) - i) else 0 := by
    intro c hc
    obtain ⟨hcX, hcc⟩ := Finset.mem_filter.1 hc
    have hp := fc_pos X d hX hcX
    by_cases hca : c ⊆ a.1
    · rw [if_pos hca]
      have := sum_up X d hX hcX i hcc
      have h3 : ∑ b ∈ faces X (i + 1),
          (if c ⊆ a.1 ∧ c ⊆ b then (fc X d b : ℝ) / (fc X d c : ℝ) else 0) =
          (∑ b ∈ faces X (i + 1), (if c ⊆ b then (fc X d b : ℝ) else 0)) / (fc X d c : ℝ) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases h : c ⊆ b <;> simp [hca, h]
      rw [h3, this]
      field_simp
    · rw [if_neg hca]
      exact Finset.sum_eq_zero fun b _ => by simp [hca]
  rw [Finset.sum_congr rfl h2, sum_down_const X d hX haX i hac]
  field_simp

lemma Wf_vdeg (hX : IsPure X d) (hi : i + 1 ≤ d) (a : faces X (i + 1)) :
    vdeg (Wf X d i) a = (fc X d a.1 : ℝ) := by
  unfold vdeg Wf
  simp only [Matrix.of_apply]
  rw [← Finset.mul_sum, W_rowsum X d hX hi, mul_one]

lemma sum2 (F : Finset V → Finset V → ℝ) :
    ∑ a : faces X (i + 1), ∑ b : faces X (i + 1), F a.1 b.1 =
      ∑ a ∈ faces X (i + 1), ∑ b ∈ faces X (i + 1), F a b := by
  have h1 : ∀ a : faces X (i + 1), ∑ b : faces X (i + 1), F a.1 b.1 =
      ∑ b ∈ faces X (i + 1), F a.1 b := fun a => Finset.sum_coe_sort (faces X (i + 1)) (F a.1)
  simp_rw [h1]
  exact Finset.sum_coe_sort (faces X (i + 1)) (fun a => ∑ b ∈ faces X (i + 1), F a b)

lemma quad_form (hX : IsPure X d) (hi : i + 1 ≤ d) (g : Finset V → ℝ) :
    ∑ a : faces X (i + 1), ∑ b : faces X (i + 1), Wf X d i a b * g a.1 * g b.1 =
      Qq X d i g := by
  have hdi : (0 : ℝ) < (d : ℝ) - i := by
    have : ((i + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast hi
    push_cast at this; linarith
  set K : ℝ := ((i : ℝ) + 1) * ((d : ℝ) - i) with hK
  have hK0 : 0 < K := by positivity
  have e := sum2 X (i := i) (fun a b => (1 / K * ∑ c ∈ faces X i,
    (if c ⊆ a ∧ c ⊆ b then (fc X d a : ℝ) * (fc X d b : ℝ) / (fc X d c : ℝ) else 0)) * g a * g b)
  have e1 : ∑ a : faces X (i + 1), ∑ b : faces X (i + 1), Wf X d i a b * g a.1 * g b.1 =
      ∑ a : faces X (i + 1), ∑ b : faces X (i + 1), (1 / K * ∑ c ∈ faces X i,
        (if c ⊆ a.1 ∧ c ⊆ b.1 then (fc X d a.1 : ℝ) * (fc X d b.1 : ℝ) / (fc X d c : ℝ) else 0))
          * g a.1 * g b.1 := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Wf_cform X d hX hi]
  rw [e1, e]
  unfold Qq
  rw [← hK]
  have e2 : ∀ a b : Finset V, (1 / K * ∑ c ∈ faces X i,
      (if c ⊆ a ∧ c ⊆ b then (fc X d a : ℝ) * (fc X d b : ℝ) / (fc X d c : ℝ) else 0)) * g a * g b =
      1 / K * ∑ c ∈ faces X i,
      (if c ⊆ a ∧ c ⊆ b then (fc X d a : ℝ) * (fc X d b : ℝ) / (fc X d c : ℝ) * g a * g b else 0) := by
    intro a b
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs <;> ring
  simp_rw [e2]
  simp_rw [← Finset.mul_sum]
  have e3 : ∑ a ∈ faces X (i + 1), ∑ b ∈ faces X (i + 1), ∑ c ∈ faces X i,
      (if c ⊆ a ∧ c ⊆ b then (fc X d a : ℝ) * (fc X d b : ℝ) / (fc X d c : ℝ) * g a * g b else 0) =
      ∑ c ∈ faces X i, ∑ a ∈ faces X (i + 1), ∑ b ∈ faces X (i + 1),
      (if c ⊆ a ∧ c ⊆ b then (fc X d a : ℝ) * (fc X d b : ℝ) / (fc X d c : ℝ) * g a * g b else 0) := by
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
    exact Finset.sum_comm
  have e4 : ∀ c ∈ faces X i, ∑ a ∈ faces X (i + 1), ∑ b ∈ faces X (i + 1),
      (if c ⊆ a ∧ c ⊆ b then (fc X d a : ℝ) * (fc X d b : ℝ) / (fc X d c : ℝ) * g a * g b else 0) =
      (1 / (fc X d c : ℝ)) *
        (∑ a ∈ faces X (i + 1), if c ⊆ a then (fc X d a : ℝ) * g a else 0) ^ 2 := by
    intro c hc
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h1 : c ⊆ a <;> by_cases h2 : c ⊆ b <;> simp [h1, h2]
    ring
  rw [e3, Finset.sum_congr rfl e4]

end induction

section spectral

lemma lam_eq {ι : Type*} [Fintype ι] [inst : DecidableEq ι] (M : Matrix ι ι ℝ) :
    lambdaTwo M = if h : (symWalk M).IsHermitian ∧ 2 ≤ Fintype.card ι then
      h.1.eigenvalues₀ ⟨1, h.2⟩ else 0 := by
  unfold lambdaTwo
  congr

lemma lam_sim {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ)
    (hA : (symWalk A).IsHermitian)
    (hB : (symWalk B).IsHermitian) (hc : (symWalk A).charpoly = (symWalk B).charpoly) :
    lambdaTwo A = lambdaTwo B := by
  rw [lam_eq A, lam_eq B]
  by_cases hcard : 2 ≤ Fintype.card ι
  · rw [dif_pos ⟨hA, hcard⟩, dif_pos ⟨hB, hcard⟩]
    have h := (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff hA hB).2 hc
    have h2 := congrFun h ((Fintype.equivOfCardEq (Fintype.card_fin _)) ⟨1, hcard⟩)
    simpa [Matrix.IsHermitian.eigenvalues] using h2
  · rw [dif_neg (fun h => hcard h.2), dif_neg (fun h => hcard h.2)]

lemma sim_charpoly (X : Finset (Finset V)) (d i : ℕ) (hX : IsPure X d) (hi : i + 1 ≤ d) :
    (symWalk (wDownUp X d (i + 1))).charpoly = (symWalk (Wf X d i)).charpoly := by
  have h1 : symWalk (wDownUp X d (i + 1)) = wDownUp X d (i + 1) := by
    ext a b
    have : vdeg (wDownUp X d (i + 1)) a = 1 := W_rowsum X d hX hi a
    have h2 : vdeg (wDownUp X d (i + 1)) b = 1 := W_rowsum X d hX hi b
    simp [symWalk, this, h2]
  have hfc : ∀ a : faces X (i + 1), 0 < (fc X d a.1 : ℝ) := fun a =>
    lt_of_lt_of_le one_pos (fc_pos X d hX (Finset.mem_filter.1 a.2).1)
  set Dh : Matrix (faces X (i + 1)) (faces X (i + 1)) ℝ :=
    Matrix.diagonal (fun a => Real.sqrt (fc X d a.1 : ℝ)) with hDh
  set Di : Matrix (faces X (i + 1)) (faces X (i + 1)) ℝ :=
    Matrix.diagonal (fun a => 1 / Real.sqrt (fc X d a.1 : ℝ)) with hDi
  have h3 : symWalk (Wf X d i) = Dh * wDownUp X d (i + 1) * Di := by
    ext a b
    rw [hDh, hDi, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [symWalk, Matrix.of_apply, Wf_vdeg X d hX hi]
    unfold Wf
    simp only [Matrix.of_apply]
    have ha := hfc a
    have hb := hfc b
    have hsa : Real.sqrt (fc X d a.1 : ℝ) * Real.sqrt (fc X d a.1 : ℝ) = (fc X d a.1 : ℝ) :=
      Real.mul_self_sqrt ha.le
    have hsa0 : 0 < Real.sqrt (fc X d a.1 : ℝ) := Real.sqrt_pos.2 ha
    have hsb0 : 0 < Real.sqrt (fc X d b.1 : ℝ) := Real.sqrt_pos.2 hb
    have key : ∀ (x w sa sb : ℝ), 0 < sa → 0 < sb → x = sa * sa →
        x * w / (sa * sb) = sa * w * (1 / sb) := by
      intro x w sa sb h1 h2 h3
      subst h3; field_simp
    exact key _ _ _ _ hsa0 hsb0 hsa.symm
  have h4 : Di * Dh = 1 := by
    rw [hDh, hDi, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext a
    have := Real.sqrt_pos.2 (hfc a)
    field_simp
  rw [h1, h3, Matrix.charpoly_mul_comm (Dh * wDownUp X d (i + 1)) Di, ← Matrix.mul_assoc, h4,
    Matrix.one_mul]

lemma gap_ge (X : Finset (Finset V)) (d i : ℕ) (hX : IsPure X d) (hi : i + 1 ≤ d) (κ : ℝ)
    (hκ1 : κ ≤ 1)
    (hR : ∀ g : Finset V → ℝ, ∑ a ∈ faces X (i + 1), (fc X d a : ℝ) * g a = 0 →
      Qq X d i g ≤ (1 - κ) * Nn X d (i + 1) g) :
    κ ≤ spectralGap (wDownUp X d (i + 1)) := by
  classical
  unfold spectralGap
  by_cases hH : (symWalk (wDownUp X d (i + 1))).IsHermitian ∧
      2 ≤ Fintype.card (faces X (i + 1))
  swap
  · have : lambdaTwo (wDownUp X d (i + 1)) = 0 := by
      unfold lambdaTwo; rw [dif_neg hH]
    rw [this]; linarith
  obtain ⟨hHerm, hcard⟩ := hH
  have hfc : ∀ a : faces X (i + 1), 0 < (fc X d a.1 : ℝ) := fun a =>
    lt_of_lt_of_le one_pos (fc_pos X d hX (Finset.mem_filter.1 a.2).1)
  have hWfH : (symWalk (Wf X d i)).IsHermitian := by
    refine Matrix.IsHermitian.ext fun a b => ?_
    simp only [star_trivial, symWalk, Matrix.of_apply]
    try rw [Wf_symm X d hX hi a b, mul_comm (Real.sqrt _)]
  have hlam := lam_sim _ (Wf X d i) hHerm hWfH (sim_charpoly X d i hX hi)
  rw [hlam]
  have hL := SteurerHDX.lemma_2_1 (Wf X d i) hcard (Wf_symm X d hX hi) (Wf_nonneg X d hX hi)
    (fun a => by rw [Wf_vdeg X d hX hi]; exact hfc a)
  obtain ⟨f, hf0, hf1, hfE⟩ := hL.1.1
  set D : ℝ := ∑ y, vdeg (Wf X d i) y with hD
  have hDfc : D = ∑ a : faces X (i + 1), (fc X d a.1 : ℝ) := by
    rw [hD]; exact Finset.sum_congr rfl fun a _ => Wf_vdeg X d hX hi a
  have hD0 : 0 < D := by
    rw [hD]
    haveI : Nonempty (faces X (i + 1)) := Fintype.card_pos_iff.1 (by omega)
    exact Finset.sum_pos (fun a _ => by rw [Wf_vdeg X d hX hi]; exact hfc a)
      ⟨Classical.arbitrary _, by simp⟩
  set g : Finset V → ℝ := fun v => if hv : v ∈ faces X (i + 1) then f ⟨v, hv⟩ else 0 with hgdef
  have hg : ∀ a : faces X (i + 1), g a.1 = f a := fun a => by simp [hgdef]
  have hsd : ∀ a, statDist (Wf X d i) a = (fc X d a.1 : ℝ) / D := fun a => by
    unfold statDist; rw [Wf_vdeg X d hX hi]
  -- mean zero
  have hmean : ∑ a ∈ faces X (i + 1), (fc X d a : ℝ) * g a = 0 := by
    have h1 : innerMu (Wf X d i) f (fun _ => 1) = (1 / D) * ∑ a : faces X (i + 1), (fc X d a.1 : ℝ) * f a := by
      unfold innerMu
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hsd]; ring
    rw [h1] at hf1
    have h2 : ∑ a : faces X (i + 1), (fc X d a.1 : ℝ) * f a = 0 := by
      rcases mul_eq_zero.1 hf1 with h | h
      · exact absurd h (one_div_pos.2 hD0).ne'
      · exact h
    have h3 : ∑ a : faces X (i + 1), (fc X d a.1 : ℝ) * g a.1 =
        ∑ a ∈ faces X (i + 1), (fc X d a : ℝ) * g a :=
      Finset.sum_coe_sort (faces X (i + 1)) (fun v => (fc X d v : ℝ) * g v)
    rw [← h3, ← h2]
    exact Finset.sum_congr rfl fun a _ => by rw [hg]
  have hN : Nn X d (i + 1) g = ∑ a : faces X (i + 1), (fc X d a.1 : ℝ) * f a ^ 2 := by
    unfold Nn
    rw [← Finset.sum_coe_sort (faces X (i + 1)) (fun v => (fc X d v : ℝ) * g v ^ 2)]
    exact Finset.sum_congr rfl fun a _ => by rw [hg]
  have hNpos : 0 < Nn X d (i + 1) g := by
    rw [hN]
    obtain ⟨a0, ha0⟩ : ∃ a, f a ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hf0 (funext hcon)
    have hnn : ∀ a ∈ (Finset.univ : Finset (faces X (i + 1))), 0 ≤ (fc X d a.1 : ℝ) * f a ^ 2 :=
      fun a _ => by have := hfc a; positivity
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum hnn (Finset.mem_univ a0))
    have := hfc a0
    have : 0 < f a0 ^ 2 := by positivity
    positivity
  have hE : GibbsCongestion.dirichletForm (walk (Wf X d i)) (statDist (Wf X d i)) f f =
      (1 / D) * (Nn X d (i + 1) g - Qq X d i g) := by
    rw [E_expand (Wf X d i) (Wf_symm X d hX hi) (fun a => by
      rw [Wf_vdeg X d hX hi]; exact hfc a) f, ← hD, hN, ← quad_form X d hX hi g]
    congr 2
    · exact Finset.sum_congr rfl fun a _ => by rw [Wf_vdeg X d hX hi]
    · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hg, hg]
  have hI : innerMu (Wf X d i) f f = (1 / D) * Nn X d (i + 1) g := by
    unfold innerMu
    rw [hN, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hsd]; ring
  rw [hfE, hE, hI]
  have hQ := hR g hmean
  rw [mul_div_mul_left _ _ (one_div_pos.2 hD0).ne', le_div_iff₀ hNpos]
  linarith

end spectral

end LG
/-- W2: Alev–Lau Theorem 3.1 for the weighted complex (Π induced from uniform on X(d)). -/
theorem levels_gap (X : Finset (Finset V)) (d : ℕ) (hX : IsPure X d) (γ : ℕ → ℝ)
    (h0 : ∀ i, 0 ≤ γ i) (h1 : ∀ i, γ i ≤ 1) (j : ℕ) (hj1 : 1 ≤ j) (hjd : j ≤ d)
    (hγ : ∀ α ∈ X, α.card + 2 ≤ j → wLam X d α ≤ γ α.card) :
    (1 / (j : ℝ)) * ∏ i ∈ Finset.range (j - 1), (1 - γ i) ≤ spectralGap (wDownUp X d j) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hk : (1 / ((i + 1 : ℕ) : ℝ)) * ∏ m ∈ Finset.range (i + 1 - 1), (1 - γ m) =
      LG.kap γ i := by
    unfold LG.kap
    simp
  rw [hk]
  exact LG.gap_ge X d i hX hjd _ (LG.kap_le_one γ h0 h1 i)
    (LG.rayleigh_levels X d hX γ h0 h1 (i + 1) hjd hγ i le_rfl)
/-- W0a: at the top level the weights are all 1 and the weighted walk is `downUp`. -/
theorem fc_top (X : Finset (Finset V)) (d : ℕ) (b : Finset V) (hb : b ∈ faces X d) :
    fc X d b = 1 := by
  unfold fc
  rw [Finset.card_eq_one]
  refine ⟨b, ?_⟩
  ext σ
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hσ, hs⟩
    have h1 := (Finset.mem_filter.1 hσ).2
    have h2 := (Finset.mem_filter.1 hb).2
    exact (Finset.eq_of_subset_of_card_le hs (by omega)).symm
  · rintro rfl
    exact ⟨hb, subset_rfl⟩

theorem wDownUp_top (X : Finset (Finset V)) (d : ℕ) : wDownUp X d d = downUp X d := by
  ext a b
  simp only [wDownUp, downUp, Matrix.of_apply]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs with h
  · rw [fc_top X d b.1 b.2]
    have : ∀ ρ ∈ (faces X d).filter (fun ρ => a.1.erase v ⊆ ρ), (fc X d ρ : ℝ) = 1 := by
      intro ρ hρ
      rw [fc_top X d ρ (Finset.mem_filter.1 hρ).1]; simp
    rw [Finset.sum_congr rfl this]
    simp
  · rfl

/-- W0b: at codimension 2 the weighted link walk is the simple random walk. -/
theorem wLam_top (X : Finset (Finset V)) (d : ℕ) (α : Finset V) (hα : α ∈ X)
    (hc : α.card + 2 = d) : wLam X d α = lambdaTau X α := by
  classical
  unfold wLam lambdaTau
  congr 1
  ext x y
  have hadj : (skeleton1 (link X α)).Adj x y ↔ (x ≠ y ∧ x.1 ∪ y.1 ∈ link X α) := Iff.rfl
  simp only [wLinkAdj, Matrix.of_apply, SimpleGraph.adjMatrix_apply]
  by_cases h : x ≠ y ∧ x.1 ∪ y.1 ∈ link X α
  · rw [if_pos h, if_pos (hadj.2 h)]
    obtain ⟨hne, hmem⟩ := h
    obtain ⟨σ, hσ, hσe⟩ := Finset.mem_image.1 hmem
    obtain ⟨hσX, hασ⟩ := Finset.mem_filter.1 hσ
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (Finset.mem_filter.1 x.2).2
    obtain ⟨b, hb⟩ := Finset.card_eq_one.1 (Finset.mem_filter.1 y.2).2
    have hab : a ≠ b := by
      intro e
      apply hne
      apply Subtype.ext
      rw [ha, hb, e]
    have hxy : (x.1 ∪ y.1).card = 2 := by
      rw [ha, hb]
      simp [Finset.card_pair hab]
    have hcs := Finset.card_sdiff_add_card_eq_card hασ
    rw [hσe, hxy] at hcs
    have hu : α ∪ x.1 ∪ y.1 = σ := by
      rw [Finset.union_assoc, ← hσe]
      exact Finset.union_sdiff_of_subset hασ
    rw [hu, fc_top X d σ (Finset.mem_filter.2 ⟨hσX, by omega⟩)]
    simp
  · rw [if_neg h, if_neg (fun h' => h (hadj.1 h'))]

/-- W1: Oppenheim's trickling-down (Garland method), weighted form.  Needs the link of `α`
to have facets of size >= 3 (`α.card + 3 ≤ d`), `α`-link connected, all vertex-link graphs
`≤ g < 1`. -/
lemma prod_tele (γ : ℝ) (hγ0 : 0 ≤ γ) (d : ℕ) (hγ : ((d : ℝ) - 1) * γ < 1) (n : ℕ)
    (hn : n + 1 ≤ d) :
    ∏ i ∈ Finset.range n, (1 - γ / (1 - ((d : ℝ) - 2 - i) * γ)) =
      (1 - ((d : ℝ) - 1) * γ) / (1 - ((d : ℝ) - 1 - n) * γ) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty, Nat.cast_zero, sub_zero]
    have : (1 - ((d : ℝ) - 1) * γ) ≠ 0 := by linarith
    field_simp
  | succ n ih =>
    have hn' : n + 1 ≤ d := by omega
    rw [Finset.prod_range_succ, ih hn']
    have hnr : (n : ℝ) + 1 ≤ d := by exact_mod_cast hn'
    have h1 : 0 < 1 - ((d : ℝ) - 1 - n) * γ := by
      have : ((d : ℝ) - 1 - n) * γ ≤ ((d : ℝ) - 1) * γ := by
        apply mul_le_mul_of_nonneg_right _ hγ0
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      linarith
    have h2 : 0 < 1 - ((d : ℝ) - 2 - n) * γ := by nlinarith
    have h3 : 1 - ((d : ℝ) - 1 - ((n + 1 : ℕ) : ℝ)) * γ = 1 - ((d : ℝ) - 2 - n) * γ := by
      push_cast; ring
    rw [h3]
    have h4 : 1 - γ / (1 - ((d : ℝ) - 2 - n) * γ) =
        (1 - ((d : ℝ) - 1 - n) * γ) / (1 - ((d : ℝ) - 2 - n) * γ) := by
      rw [eq_div_iff h2.ne', sub_mul, div_mul_cancel₀ _ h2.ne']; ring
    rw [h4, div_mul_div_comm, div_eq_div_iff (mul_pos h1 h2).ne' h2.ne']
    ring

end SteurerHDX.Dev.T23

namespace SteurerHDX
open Dev.T23

theorem chk_theorem_2_3 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (d : ℕ) (δ : ℝ)
    (hX : IsPure X d) (hconn : IsConnectedComplex X d) (hcard : 2 ≤ (faces X d).card)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hexp : IsTopLinkExpander X d ((1 - δ) / d)) :
    (max 0 (1 - (1 - δ) / (δ * d))) ^ d / d ≤ spectralGap (downUp X d) ∧
      (δ = 1 / 2 → 1 / (Real.exp 1 * d) ≤ spectralGap (downUp X d)) := by
  have hd : 1 ≤ d := by
    by_contra h
    have h0 : d = 0 := by omega
    subst h0
    have : faces X 0 ⊆ {∅} := by
      intro τ hτ
      have := (Finset.mem_filter.1 hτ).2
      simp [Finset.card_eq_zero.1 this]
    have := Finset.card_le_card this
    simp at this
    omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set γ : ℝ := (1 - δ) / d with hγdef
  have hγ0 : 0 < γ := div_pos (by linarith) hdpos
  have hγ1 : ((d : ℝ) - 1) * γ < 1 := by
    rw [hγdef, ← mul_div_assoc, div_lt_one hdpos]
    nlinarith
  -- trickling down
  have claim : ∀ m : ℕ, ∀ α ∈ X, α.card + 2 + m = d →
      wLam X d α ≤ γ / (1 - (m : ℝ) * γ) := by
    intro m
    induction m with
    | zero =>
      intro α hα hc
      rw [wLam_top X d α hα (by omega)]
      simpa using hexp α hα (by omega)
    | succ m ih =>
      intro α hα hc
      have hmr : ((m : ℝ) + 1) + 2 ≤ d := by
        have : α.card + 2 + (m + 1) = d := hc
        have : m + 1 + 2 ≤ d := by omega
        exact_mod_cast this
      have hmg : 0 < 1 - (m : ℝ) * γ := by nlinarith
      have hmg' : 0 < 1 - ((m : ℝ) + 1) * γ := by nlinarith
      have hg1 : γ / (1 - (m : ℝ) * γ) < 1 := by
        rw [div_lt_one hmg]; nlinarith
      have key := trickle_step X d hX α hα (by omega)
        (hconn α hα (by omega)) _ hg1 (fun β hβ _ hβc => ih β hβ (by omega))
      refine key.trans (le_of_eq ?_)
      have e : 1 - γ / (1 - (m : ℝ) * γ) = ((1 - (m : ℝ) * γ) - γ) / (1 - (m : ℝ) * γ) := by
        rw [eq_div_iff hmg.ne', sub_mul, div_mul_cancel₀ _ hmg.ne']; ring
      rw [e, div_div_div_cancel_right₀ hmg.ne']
      push_cast
      congr 1
      ring
  set γ' : ℕ → ℝ := fun i => γ / (1 - ((d : ℝ) - 2 - i) * γ) with hγ'
  have hden : ∀ i : ℕ, 0 < 1 - ((d : ℝ) - 2 - i) * γ := by
    intro i
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    nlinarith
  have hg0 : ∀ i, 0 ≤ γ' i := fun i => div_nonneg hγ0.le (hden i).le
  have hg1' : ∀ i, γ' i ≤ 1 := by
    intro i
    simp only [hγ']
    rw [div_le_one (hden i)]
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    nlinarith
  have hlev := levels_gap X d hX γ' hg0 hg1' d hd le_rfl (by
    intro α hα hc
    have hm := claim (d - (α.card + 2)) α hα (by omega)
    have hcast : ((d - (α.card + 2) : ℕ) : ℝ) = (d : ℝ) - 2 - α.card := by
      rw [Nat.cast_sub hc]; push_cast; ring
    rw [hcast] at hm
    exact hm)
  rw [wDownUp_top] at hlev
  rw [prod_tele γ hγ0.le d hγ1 (d - 1) (by omega)] at hlev
  have hcast2 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub hd]; simp
  rw [hcast2] at hlev
  simp only [sub_self, zero_mul, sub_zero, div_one] at hlev
  -- hlev : 1/d * (1 - (d-1) γ) ≤ gap
  have hγeq : ((d : ℝ) - 1) * γ = ((d : ℝ) - 1) * (1 - δ) / d := by
    rw [hγdef]; ring
  have hA : 1 / (d : ℝ) * (1 - ((d : ℝ) - 1) * γ) = (1 + ((d : ℝ) - 1) * δ) / d ^ 2 := by
    rw [hγeq]; field_simp; ring
  rw [hA] at hlev
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  constructor
  · refine le_trans ?_ hlev
    -- (max 0 (1 - t))^d / d ≤ (1 + (d-1) δ) / d^2
    have hδd : (1 + ((d : ℝ) - 1) * δ) / d ^ 2 ≥ δ / d := by
      rw [ge_iff_le, div_le_div_iff₀ hdpos (by positivity)]
      nlinarith
    refine le_trans ?_ hδd
    apply div_le_div_of_nonneg_right _ hdpos.le
    set t : ℝ := (1 - δ) / (δ * d) with ht
    have ht0 : 0 ≤ t := div_nonneg (by linarith) (by positivity)
    rcases le_or_gt (1 - t) 0 with h | h
    · rw [max_eq_left h, zero_pow (by omega)]; linarith
    · rw [max_eq_right h.le]
      have h1 : (1 - t) * (1 + t) ≤ 1 := by nlinarith
      have h2 : (1 - t) ^ d * (1 + t) ^ d ≤ 1 := by
        rw [← mul_pow]; exact pow_le_one₀ (by nlinarith) h1
      have h3 : 1 + d * t ≤ (1 + t) ^ d := one_add_mul_le_pow (by linarith) d
      have h4 : 1 + d * t = 1 / δ := by
        rw [ht]; field_simp; ring
      have h5 : (1 - t) ^ d ≥ 0 := pow_nonneg h.le d
      have h6 : (1 - t) ^ d * (1 / δ) ≤ 1 := by
        calc _ ≤ (1 - t) ^ d * (1 + t) ^ d := by
              apply mul_le_mul_of_nonneg_left _ h5; linarith
          _ ≤ 1 := h2
      rw [mul_one_div, div_le_one hδ0] at h6
      exact h6
  · intro hδ
    refine le_trans ?_ hlev
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.exp_one_gt_d9; linarith
    rw [hδ]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hdpos hdpos]

end SteurerHDX
end

theorem solution : type_of% @SteurerHDX.chk_theorem_2_3 := @SteurerHDX.chk_theorem_2_3
