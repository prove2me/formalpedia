-- Prove2me | solution 1 for SteurerHDX.theorem_2_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T23:19:12.13221+00:00
-- url     : https://prove2.me/submissions/d2edbe26-93f9-471e-a8b4-6b1330cdfb7c

import Mathlib
import Definitions.Def_SteurerHDX_IsConnectedComplex
import Definitions.Def_SteurerHDX_flagsComplex
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_SteurerHDX_IsPartite
import Definitions.Def_SteurerHDX_degree
import Definitions.Def_SteurerHDX_IsTopLinkExpander
import Definitions.Def_SteurerHDX_lambdaTwo
import Definitions.Def_SteurerHDX_downUp
import Definitions.Def_SteurerHDX_spectralGap
import Theorems.Thm_SteurerHDX_section_2_3_flags
import Theorems.Thm_SteurerHDX_theorem_2_3

section
set_option autoImplicit false
namespace SteurerHDX.Dev.T24
open Module

section Basic
variable {F E : Type*} [Field F] [AddCommGroup E] [Module F E] [FiniteDimensional F E]

lemma finrank_sup_span_of_not_mem (U : Submodule F E) (x : E) (hx : x ∉ U) :
    finrank F (U ⊔ Submodule.span F {x} : Submodule F E) = finrank F U + 1 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq U (Submodule.span F {x})
  have hd : Disjoint U (Submodule.span F {x}) :=
    Submodule.disjoint_span_singleton.2 (fun h => absurd h hx)
  have hx0 : x ≠ 0 := fun h => hx (h ▸ U.zero_mem)
  rw [hd.eq_bot, finrank_bot, finrank_span_singleton hx0] at h
  omega

lemma exists_between_aux (n : ℕ) : ∀ (A B : Submodule F E), A ≤ B →
    finrank F A + n ≤ finrank F B →
    ∃ U : Submodule F E, A ≤ U ∧ U ≤ B ∧ finrank F U = finrank F A + n := by
  induction n with
  | zero => intro A B hAB _; exact ⟨A, le_rfl, hAB, by simp⟩
  | succ n ih =>
    intro A B hAB hn
    obtain ⟨U, hAU, hUB, hU⟩ := ih A B hAB (by omega)
    have hlt : U < B := by
      refine lt_of_le_of_ne hUB ?_
      rintro rfl; omega
    obtain ⟨x, hxB, hxU⟩ := SetLike.exists_of_lt hlt
    refine ⟨U ⊔ Submodule.span F {x}, hAU.trans le_sup_left,
      sup_le hUB ((Submodule.span_singleton_le_iff_mem _ _).2 hxB), ?_⟩
    rw [finrank_sup_span_of_not_mem U x hxU, hU]; ring

lemma exists_between (A B : Submodule F E) (g : ℕ) (hAB : A ≤ B)
    (h1 : finrank F A ≤ g) (h2 : g ≤ finrank F B) :
    ∃ U : Submodule F E, A ≤ U ∧ U ≤ B ∧ finrank F U = g := by
  obtain ⟨U, h1, h2, h3⟩ := exists_between_aux (g - finrank F A) A B hAB (by omega)
  exact ⟨U, h1, h2, by omega⟩

lemma le_antisymm_dim {A B : Submodule F E} (h : A ≤ B) (hd : finrank F B ≤ finrank F A) : A = B :=
  Submodule.eq_of_le_of_finrank_le h hd

lemma comp_eq_of_finrank {A B : Submodule F E} (h : A ≤ B ∨ B ≤ A)
    (hd : finrank F A = finrank F B) : A = B := by
  rcases h with h | h
  · exact le_antisymm_dim h hd.ge
  · exact (le_antisymm_dim h hd.le).symm

/-- chain with allowed dimensions -/
def ChainOK (S : Finset ℕ) (s : Finset (Submodule F E)) : Prop :=
  (∀ W ∈ s, finrank F W ∈ S) ∧ ∀ W ∈ s, ∀ W' ∈ s, W ≤ W' ∨ W' ≤ W

/-- W is compatible with the chain τ and has a free dimension -/
def Cp (S : Finset ℕ) (τ : Finset (Submodule F E)) (W : Submodule F E) : Prop :=
  finrank F W ∈ S ∧ (∀ V ∈ τ, finrank F V ≠ finrank F W) ∧ ∀ V ∈ τ, W ≤ V ∨ V ≤ W

noncomputable def lo (τ : Finset (Submodule F E)) (g : ℕ) : Submodule F E :=
  (τ.filter (fun V : Submodule F E => finrank F V < g)).sup id

noncomputable def hi (τ : Finset (Submodule F E)) (g : ℕ) : Submodule F E :=
  (τ.filter (fun V : Submodule F E => g < finrank F V)).inf id

variable {S : Finset ℕ} {τ : Finset (Submodule F E)}

lemma lo_spec (hτ : ∀ W ∈ τ, ∀ W' ∈ τ, W ≤ W' ∨ W' ≤ W) (g : ℕ) :
    lo τ g = ⊥ ∨ (lo τ g ∈ τ ∧ finrank F (lo τ g) < g) := by
  unfold lo
  refine Finset.sup_induction (p := fun x : Submodule F E => x = ⊥ ∨ (x ∈ τ ∧ finrank F x < g))
    (Or.inl rfl) ?_ ?_
  · rintro a (rfl | ⟨ha, ha'⟩) b (rfl | ⟨hb, hb'⟩)
    · simp
    · rw [bot_sup_eq]; exact Or.inr ⟨hb, hb'⟩
    · rw [sup_bot_eq]; exact Or.inr ⟨ha, ha'⟩
    · rcases hτ a ha b hb with h | h
      · rw [sup_eq_right.2 h]; exact Or.inr ⟨hb, hb'⟩
      · rw [sup_eq_left.2 h]; exact Or.inr ⟨ha, ha'⟩
  · intro V hV
    simp only [Finset.mem_filter] at hV
    exact Or.inr ⟨hV.1, hV.2⟩

lemma le_lo {g : ℕ} {V : Submodule F E} (hV : V ∈ τ) (hg : finrank F V < g) : V ≤ lo τ g :=
  Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨hV, hg⟩)

lemma hi_spec (hτ : ∀ W ∈ τ, ∀ W' ∈ τ, W ≤ W' ∨ W' ≤ W) (g : ℕ) :
    hi τ g = ⊤ ∨ (hi τ g ∈ τ ∧ g < finrank F (hi τ g)) := by
  unfold hi
  refine Finset.inf_induction (p := fun x : Submodule F E => x = ⊤ ∨ (x ∈ τ ∧ g < finrank F x))
    (Or.inl rfl) ?_ ?_
  · rintro a (rfl | ⟨ha, ha'⟩) b (rfl | ⟨hb, hb'⟩)
    · simp
    · rw [top_inf_eq]; exact Or.inr ⟨hb, hb'⟩
    · rw [inf_top_eq]; exact Or.inr ⟨ha, ha'⟩
    · rcases hτ a ha b hb with h | h
      · rw [inf_eq_left.2 h]; exact Or.inr ⟨ha, ha'⟩
      · rw [inf_eq_right.2 h]; exact Or.inr ⟨hb, hb'⟩
  · intro V hV
    simp only [Finset.mem_filter] at hV
    exact Or.inr ⟨hV.1, hV.2⟩

lemma hi_le {g : ℕ} {V : Submodule F E} (hV : V ∈ τ) (hg : g < finrank F V) : hi τ g ≤ V :=
  Finset.inf_le (f := id) (Finset.mem_filter.2 ⟨hV, hg⟩)

/-- characterisation via the interval [lo, hi] -/
lemma cp_of_between (hτ : ChainOK S τ) {g : ℕ} (hgS : g ∈ S) (hfree : ∀ V ∈ τ, finrank F V ≠ g)
    {U : Submodule F E} (hU : finrank F U = g) (h1 : lo τ g ≤ U) (h2 : U ≤ hi τ g) :
    Cp S τ U := by
  refine ⟨hU ▸ hgS, fun V hV => hU ▸ hfree V hV, fun V hV => ?_⟩
  rcases lt_trichotomy (finrank F V) g with h | h | h
  · exact Or.inr ((le_lo hV h).trans h1)
  · exact absurd h (hfree V hV)
  · exact Or.inl (h2.trans (hi_le hV h))

lemma lo_le_of_cp (hτ : ChainOK S τ) {U : Submodule F E} (hU : Cp S τ U) :
    lo τ (finrank F U) ≤ U := by
  rcases lo_spec hτ.2 (finrank F U) with h | ⟨hm, hd⟩
  · rw [h]; exact bot_le
  · rcases hU.2.2 _ hm with h | h
    · exact absurd (Submodule.finrank_mono h) (by omega)
    · exact h

lemma le_hi_of_cp (hτ : ChainOK S τ) {U : Submodule F E} (hU : Cp S τ U) :
    U ≤ hi τ (finrank F U) := by
  rcases hi_spec hτ.2 (finrank F U) with h | ⟨hm, hd⟩
  · rw [h]; exact le_top
  · rcases hU.2.2 _ hm with h | h
    · exact h
    · exact absurd (Submodule.finrank_mono h) (by omega)

lemma lo_le_hi (hτ : ChainOK S τ) (g : ℕ) : lo τ g ≤ hi τ g := by
  rcases lo_spec hτ.2 g with h | ⟨h1, h2⟩
  · rw [h]; exact bot_le
  · rcases hi_spec hτ.2 g with h' | ⟨h3, h4⟩
    · rw [h']; exact le_top
    · rcases hτ.2 _ h1 _ h3 with h | h
      · exact h
      · exact absurd (Submodule.finrank_mono h) (by omega)

lemma le_finrank_hi (hτ : ChainOK S τ) {g : ℕ} (hg : g ≤ finrank F E) : g ≤ finrank F (hi τ g) := by
  rcases hi_spec hτ.2 g with h | ⟨h1, h2⟩
  · rw [h]; simpa using hg
  · exact h2.le


lemma finrank_lo_le (hτ : ChainOK S τ) (g : ℕ) : finrank F (lo τ g) ≤ g := by
  rcases lo_spec hτ.2 g with h | ⟨h1, h2⟩
  · rw [h]; simp
  · exact h2.le

lemma lo_le_of_lt (hτ : ChainOK S τ) {W : Submodule F E} (hW : Cp S τ W) {g : ℕ}
    (hg : g < finrank F W) : lo τ g ≤ W := by
  rcases lo_spec hτ.2 g with h | ⟨h1, h2⟩
  · rw [h]; exact bot_le
  · rcases hW.2.2 _ h1 with h | h
    · exact absurd (Submodule.finrank_mono h) (by omega)
    · exact h

lemma le_hi_of_lt (hτ : ChainOK S τ) {W : Submodule F E} (hW : Cp S τ W) {g : ℕ}
    (hg : finrank F W < g) : W ≤ hi τ g := by
  rcases hi_spec hτ.2 g with h | ⟨h1, h2⟩
  · rw [h]; exact le_top
  · rcases hW.2.2 _ h1 with h | h
    · exact h
    · exact absurd (Submodule.finrank_mono h) (by omega)

lemma lo_cmp (hτ : ChainOK S τ) {W : Submodule F E} (hW : Cp S τ W) (g : ℕ) :
    lo τ g ≤ W ∨ W ≤ lo τ g := by
  rcases lo_spec hτ.2 g with h | ⟨h1, h2⟩
  · rw [h]; exact Or.inl bot_le
  · rcases hW.2.2 _ h1 with h | h
    · exact Or.inr h
    · exact Or.inl h

lemma hi_cmp (hτ : ChainOK S τ) {W : Submodule F E} (hW : Cp S τ W) (g : ℕ) :
    hi τ g ≤ W ∨ W ≤ hi τ g := by
  rcases hi_spec hτ.2 g with h | ⟨h1, h2⟩
  · rw [h]; exact Or.inr le_top
  · rcases hW.2.2 _ h1 with h | h
    · exact Or.inr h
    · exact Or.inl h

lemma sup_cmp {x A B : Submodule F E} (hA : x ≤ A ∨ A ≤ x) (hB : x ≤ B ∨ B ≤ x)
    (hd : finrank F A = finrank F B) : x ≤ A ⊔ B ∨ A ⊔ B ≤ x := by
  rcases hA with hA | hA
  · exact Or.inl (hA.trans le_sup_left)
  · rcases hB with hB | hB
    · have : A = B := comp_eq_of_finrank (Or.inl (hA.trans hB)) hd
      subst this; simp [hA]
    · exact Or.inr (sup_le hA hB)

lemma inf_cmp {x A B : Submodule F E} (hA : x ≤ A ∨ A ≤ x) (hB : x ≤ B ∨ B ≤ x)
    (hd : finrank F A = finrank F B) : x ≤ A ⊓ B ∨ A ⊓ B ≤ x := by
  rcases hA with hA | hA
  · rcases hB with hB | hB
    · exact Or.inl (le_inf hA hB)
    · have : A = B := comp_eq_of_finrank (Or.inr (hB.trans hA)) hd
      subst this; simp [hA]
  · exact Or.inr (inf_le_left.trans hA)

lemma pair_move (hτ : ChainOK S τ) (hE : ∀ g ∈ S, g ≤ finrank F E)
    {W₁ W₂ : Submodule F E} (h₁ : Cp S τ W₁) (h₂ : Cp S τ W₂)
    (hd : finrank F W₁ = finrank F W₂) {f : ℕ} (hf : f ∈ S) (hfree : ∀ V ∈ τ, finrank F V ≠ f)
    (hfe : f ≠ finrank F W₁)
    (hup : finrank F W₁ < f → finrank F (W₁ ⊔ W₂ : Submodule F E) ≤ f)
    (hdn : f < finrank F W₁ → f ≤ finrank F (W₁ ⊓ W₂ : Submodule F E)) :
    ∃ U : Submodule F E, Cp S τ U ∧ finrank F U = f ∧ (W₁ ≤ U ∨ U ≤ W₁) ∧ (W₂ ≤ U ∨ U ≤ W₂) := by
  have hfE := hE f hf
  rcases lt_or_gt_of_ne hfe with hlt | hgt
  · -- f < e
    have hl1 : lo τ f ≤ W₁ := lo_le_of_lt hτ h₁ hlt
    have hl2 : lo τ f ≤ W₂ := lo_le_of_lt hτ h₂ (hd ▸ hlt)
    have hB : f ≤ finrank F (hi τ f ⊓ (W₁ ⊓ W₂) : Submodule F E) := by
      rcases inf_cmp (hi_cmp hτ h₁ f) (hi_cmp hτ h₂ f) hd with h | h
      · rw [inf_eq_left.2 h]; exact le_finrank_hi hτ hfE
      · rw [inf_eq_right.2 h]; exact hdn hlt
    obtain ⟨U, hU1, hU2, hU3⟩ := exists_between (lo τ f) (hi τ f ⊓ (W₁ ⊓ W₂)) f
      (le_inf (lo_le_hi hτ f) (le_inf hl1 hl2)) (finrank_lo_le hτ f) hB
    refine ⟨U, cp_of_between hτ hf hfree hU3 hU1 (hU2.trans inf_le_left), hU3, ?_, ?_⟩
    · exact Or.inr (hU2.trans (inf_le_right.trans inf_le_left))
    · exact Or.inr (hU2.trans (inf_le_right.trans inf_le_right))
  · -- e < f
    have hu1 : W₁ ≤ hi τ f := le_hi_of_lt hτ h₁ hgt
    have hu2 : W₂ ≤ hi τ f := le_hi_of_lt hτ h₂ (hd ▸ hgt)
    have hA : finrank F (lo τ f ⊔ (W₁ ⊔ W₂) : Submodule F E) ≤ f := by
      rcases sup_cmp (lo_cmp hτ h₁ f) (lo_cmp hτ h₂ f) hd with h | h
      · rw [sup_eq_right.2 h]; exact hup hgt
      · rw [sup_eq_left.2 h]; exact finrank_lo_le hτ f
    have hAB : lo τ f ⊔ (W₁ ⊔ W₂) ≤ hi τ f :=
      sup_le (lo_le_hi hτ f) (sup_le hu1 hu2)
    have hBf : f ≤ finrank F (hi τ f) := le_finrank_hi hτ hfE
    obtain ⟨U, hU1, hU2, hU3⟩ := exists_between (lo τ f ⊔ (W₁ ⊔ W₂)) (hi τ f) f hAB hA hBf
    refine ⟨U, cp_of_between hτ hf hfree hU3 (le_sup_left.trans hU1) hU2, hU3, ?_, ?_⟩
    · exact Or.inl ((le_sup_left.trans le_sup_right).trans hU1)
    · exact Or.inl ((le_sup_right.trans le_sup_right).trans hU1)

/-- Reachability inside the compatible vertices of the link. -/
def RG (S : Finset ℕ) (τ : Finset (Submodule F E)) : Submodule F E → Submodule F E → Prop :=
  Relation.ReflTransGen (fun A B : Submodule F E =>
    Cp S τ A ∧ Cp S τ B ∧ A ≠ B ∧ (A ≤ B ∨ B ≤ A))

lemma rg_two {A B C : Submodule F E} (hA : Cp S τ A) (hB : Cp S τ B) (hC : Cp S τ C)
    (hAB : A ≠ B) (hBC : B ≠ C) (h1 : A ≤ B ∨ B ≤ A) (h2 : B ≤ C ∨ C ≤ B) : RG S τ A C :=
  Relation.ReflTransGen.tail (Relation.ReflTransGen.single ⟨hA, hB, hAB, h1⟩) ⟨hB, hC, hBC, h2⟩

lemma same_dim (hτ : ChainOK S τ) (hE : ∀ g ∈ S, g ≤ finrank F E) {e f : ℕ} (hf : f ∈ S)
    (hfree : ∀ V ∈ τ, finrank F V ≠ f) (hfe : f ≠ e) :
    ∀ n : ℕ, ∀ W W' : Submodule F E, Cp S τ W → Cp S τ W' → finrank F W = e → finrank F W' = e →
      e - finrank F (W ⊓ W' : Submodule F E) ≤ n → RG S τ W W' := by
  intro n
  induction n with
  | zero =>
    intro W W' hW hW' he he' hn
    have hge : e ≤ finrank F (W ⊓ W' : Submodule F E) := by omega
    have h1 : W ⊓ W' = W := le_antisymm_dim (A := W ⊓ W') (B := W) inf_le_left (by omega)
    have h2 : W ⊓ W' = W' := le_antisymm_dim (A := W ⊓ W') (B := W') inf_le_right (by omega)
    have : W = W' := h1.symm.trans h2
    subst this; exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro W W' hW hW' he he' hn
    by_cases hle : e - finrank F (W ⊓ W' : Submodule F E) ≤ n
    · exact ih W W' hW hW' he he' hle
    have hm : finrank F (W ⊓ W' : Submodule F E) < e := by omega
    have hmle : finrank F (W ⊓ W' : Submodule F E) ≤ e - 1 := by omega
    obtain ⟨H, hH1, hH2, hH3⟩ := exists_between (W ⊓ W') W (e - 1) inf_le_left hmle (by omega)
    have hW'W : ¬ W' ≤ W := by
      intro h
      have : W' = W := (comp_eq_of_finrank (Or.inl h) (by omega))
      rw [this, inf_idem] at hm; omega
    obtain ⟨x, hxW', hxW⟩ := Set.not_subset.1 hW'W
    have hxH : x ∉ H := fun h => hxW (hH2 h)
    set W'' : Submodule F E := H ⊔ Submodule.span F {x} with hW''
    have hW''d : finrank F W'' = e := by
      rw [hW'', finrank_sup_span_of_not_mem H x hxH, hH3]; omega
    have hHW'' : H ≤ W'' := le_sup_left
    have hxW'' : x ∈ W'' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
    have heS : e ∈ S := he ▸ hW.1
    have hefree : ∀ V ∈ τ, finrank F V ≠ e := fun V hV => he ▸ hW.2.1 V hV
    have hlW : lo τ e ≤ W := by have := lo_le_of_cp hτ hW; rwa [he] at this
    have hlW' : lo τ e ≤ W' := by have := lo_le_of_cp hτ hW'; rwa [he'] at this
    have hhW : W ≤ hi τ e := by have := le_hi_of_cp hτ hW; rwa [he] at this
    have hhW' : W' ≤ hi τ e := by have := le_hi_of_cp hτ hW'; rwa [he'] at this
    have hCp : Cp S τ W'' := by
      refine cp_of_between hτ heS hefree hW''d ?_ ?_
      · exact (le_inf hlW hlW').trans (hH1.trans hHW'')
      · exact sup_le (hH2.trans hhW) ((Submodule.span_singleton_le_iff_mem _ _).2 (hhW' hxW'))
    have hmeas : e - finrank F (W'' ⊓ W' : Submodule F E) ≤ n := by
      have hsub : (W ⊓ W') ⊔ Submodule.span F {x} ≤ W'' ⊓ W' :=
        sup_le (le_inf (hH1.trans hHW'') inf_le_right)
          (le_inf ((Submodule.span_singleton_le_iff_mem _ _).2 hxW'')
            ((Submodule.span_singleton_le_iff_mem _ _).2 hxW'))
      have hxn : x ∉ W ⊓ W' := fun h => hxW h.1
      have := Submodule.finrank_mono hsub
      rw [finrank_sup_span_of_not_mem _ x hxn] at this
      omega
    have hrest := ih W'' W' hCp hW' hW''d he' hmeas
    have hupf : finrank F W < f → finrank F (W ⊔ W'' : Submodule F E) ≤ f := by
      intro hlt
      have : (W ⊔ W'' : Submodule F E) = W ⊔ Submodule.span F {x} := by
        apply le_antisymm
        · exact sup_le le_sup_left (sup_le (hH2.trans le_sup_left) le_sup_right)
        · exact sup_le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).2 hxW'') _
      rw [this, finrank_sup_span_of_not_mem W x hxW]; omega
    have hdnf : f < finrank F W → f ≤ finrank F (W ⊓ W'' : Submodule F E) := by
      intro hlt
      have := Submodule.finrank_mono (le_inf hH2 hHW'' : H ≤ W ⊓ W'')
      omega
    obtain ⟨U, hU, hUd, hU1, hU2⟩ := pair_move hτ hE hW hCp (by omega) hf hfree (by omega)
      hupf hdnf
    have hUW'' : U ≠ W'' := fun h => by have := congrArg (fun A : Submodule F E => finrank F A) h; omega
    have hWU : W ≠ U := fun h => by have := congrArg (fun A : Submodule F E => finrank F A) h; omega
    have h1 := rg_two hW hU hCp hWU hUW'' hU1 hU2.symm
    exact h1.trans hrest

lemma rg_all (hτ : ChainOK S τ) (hE : ∀ g ∈ S, g ≤ finrank F E)
    (hFr : ∃ f₁ f₂ : ℕ, f₁ ≠ f₂ ∧ f₁ ∈ S ∧ f₂ ∈ S ∧ (∀ V ∈ τ, finrank F V ≠ f₁) ∧
      (∀ V ∈ τ, finrank F V ≠ f₂))
    (W W' : Submodule F E) (hW : Cp S τ W) (hW' : Cp S τ W') : RG S τ W W' := by
  obtain ⟨f₁, f₂, h12, h1S, h2S, h1f, h2f⟩ := hFr
  by_cases hee : finrank F W = finrank F W'
  · have : ∃ f ∈ S, (∀ V ∈ τ, finrank F V ≠ f) ∧ f ≠ finrank F W := by
      by_cases h : f₁ = finrank F W
      · exact ⟨f₂, h2S, h2f, fun h' => h12 (h.trans h'.symm)⟩
      · exact ⟨f₁, h1S, h1f, h⟩
    obtain ⟨f, hfS, hff, hfe⟩ := this
    exact same_dim (e := finrank F W) hτ hE hfS hff hfe _ W W' hW hW' rfl hee.symm (Nat.sub_le _ _)
  · obtain ⟨U, hU, hUd, hU1, hU2⟩ := pair_move hτ hE hW' hW' rfl hW.1 (fun V hV => hW.2.1 V hV)
      hee (by intro h; rw [sup_idem]; omega) (by intro h; rw [inf_idem]; omega)
    have h1 : RG S τ W U := same_dim (e := finrank F W) hτ hE hW'.1 hW'.2.1 (fun h => hee h.symm) _
      W U hW hU rfl hUd (Nat.sub_le _ _)
    refine h1.tail ⟨hU, hW', fun h => hee (by rw [← h, hUd]), hU1.symm⟩
end Basic

section Flags
variable {F : Type*} [Field F] [Fintype F] {r k : ℕ}

abbrev Sp (F : Type*) [Field F] (r : ℕ) := Submodule F (Fin (2 * r) → F)

lemma mem_flags {s : Finset (Sp F r)} :
    s ∈ flagsComplex F r k ↔ ChainOK (Finset.Icc (r - k) (r + k)) s := by
  unfold flagsComplex ChainOK
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc]

variable [DecidableEq (Sp F r)]

lemma single_mem_link {τ : Finset (Sp F r)} (W : Sp F r) :
    ({W} : Finset (Sp F r)) ∈ SteurerHDX.link (flagsComplex F r k) τ ↔
      W ∉ τ ∧ insert W τ ∈ flagsComplex F r k := by
  unfold SteurerHDX.link
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨σ, ⟨hσ, hτσ⟩, hd⟩
    have hW : W ∈ σ \ τ := by rw [hd]; exact Finset.mem_singleton_self W
    rw [Finset.mem_sdiff] at hW
    have : insert W τ = σ := by
      ext x
      simp only [Finset.mem_insert]
      constructor
      · rintro (rfl | hx)
        · exact hW.1
        · exact hτσ hx
      · intro hx
        by_cases hxτ : x ∈ τ
        · exact Or.inr hxτ
        · have : x ∈ σ \ τ := Finset.mem_sdiff.2 ⟨hx, hxτ⟩
          rw [hd] at this
          exact Or.inl (Finset.mem_singleton.1 this)
    exact ⟨hW.2, this ▸ hσ⟩
  · rintro ⟨hW, hmem⟩
    refine ⟨insert W τ, ⟨hmem, Finset.subset_insert _ _⟩, ?_⟩
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | hx, hxτ⟩
      · rfl
      · exact absurd hx hxτ
    · rintro rfl; exact ⟨Or.inl rfl, hW⟩

lemma pair_mem_link {τ : Finset (Sp F r)} (A B : Sp F r) (hA : A ∉ τ) (hB : B ∉ τ)
    (h : insert A (insert B τ) ∈ flagsComplex F r k) :
    ({A} : Finset (Sp F r)) ∪ {B} ∈ SteurerHDX.link (flagsComplex F r k) τ := by
  unfold SteurerHDX.link
  simp only [Finset.mem_image, Finset.mem_filter]
  refine ⟨insert A (insert B τ), ⟨h, ?_⟩, ?_⟩
  · intro x hx; simp [hx]
  · ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨(rfl | rfl | hx), hxτ⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hx hxτ
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, hA⟩
      · exact ⟨Or.inr (Or.inl rfl), hB⟩

lemma cp_iff {τ : Finset (Sp F r)} (hτ : τ ∈ flagsComplex F r k) (W : Sp F r) :
    Cp (Finset.Icc (r - k) (r + k)) τ W ↔ W ∉ τ ∧ insert W τ ∈ flagsComplex F r k := by
  rw [mem_flags] at hτ ⊢
  constructor
  · intro hW
    refine ⟨fun h => hW.2.1 W h rfl, ?_, ?_⟩
    · intro V hV
      rcases Finset.mem_insert.1 hV with rfl | hV
      · exact hW.1
      · exact hτ.1 V hV
    · intro V hV V' hV'
      rcases Finset.mem_insert.1 hV with h | h1 <;> rcases Finset.mem_insert.1 hV' with h' | h1'
      · rw [h, h']; exact Or.inl le_rfl
      · rw [h]; exact hW.2.2 V' h1'
      · rw [h']; exact (hW.2.2 V h1).symm
      · exact hτ.2 V h1 V' h1'
  · rintro ⟨hW, h1, h2⟩
    refine ⟨h1 W (Finset.mem_insert_self _ _), fun V hV hd => hW ?_, fun V hV => ?_⟩
    · have : V = W := comp_eq_of_finrank (h2 V (Finset.mem_insert_of_mem hV) W
        (Finset.mem_insert_self _ _)) hd
      exact this ▸ hV
    · exact (h2 W (Finset.mem_insert_self _ _) V (Finset.mem_insert_of_mem hV))


lemma vtx_mem {τ : Finset (Sp F r)} (hτ : τ ∈ flagsComplex F r k) {W : Sp F r}
    (hW : Cp (Finset.Icc (r - k) (r + k)) τ W) :
    ({W} : Finset (Sp F r)) ∈ SteurerHDX.faces (SteurerHDX.link (flagsComplex F r k) τ) 1 := by
  unfold SteurerHDX.faces
  exact Finset.mem_filter.2 ⟨(single_mem_link W).2 ((cp_iff hτ W).1 hW), Finset.card_singleton _⟩

lemma vtx_cp {τ : Finset (Sp F r)} (hτ : τ ∈ flagsComplex F r k)
    (s : SteurerHDX.faces (SteurerHDX.link (flagsComplex F r k) τ) 1) :
    ∃ W, s.1 = {W} ∧ Cp (Finset.Icc (r - k) (r + k)) τ W := by
  have hs := s.2
  unfold SteurerHDX.faces at hs
  rw [Finset.mem_filter] at hs
  obtain ⟨W, hW⟩ := Finset.card_eq_one.1 hs.2
  refine ⟨W, hW, (cp_iff hτ W).2 ?_⟩
  rw [← single_mem_link (k := k)]
  rw [← hW]; exact hs.1

theorem flags_connected (hk : 1 ≤ k) (hkr : k < r) :
    SteurerHDX.IsConnectedComplex (flagsComplex F r k) (2 * k + 1) := by
  intro τ hτ hcard
  set S := Finset.Icc (r - k) (r + k) with hS
  have hchain : ChainOK S τ := mem_flags.1 hτ
  have hE : ∀ g ∈ S, g ≤ finrank F (Fin (2 * r) → F) := by
    intro g hg
    rw [Module.finrank_fin_fun]
    rw [hS, Finset.mem_Icc] at hg; omega
  have hinj : Set.InjOn (fun V : Sp F r => finrank F V) τ := by
    intro V hV V' hV' h
    exact comp_eq_of_finrank (hchain.2 V hV V' hV') h
  have hsub : τ.image (fun V : Sp F r => finrank F V) ⊆ S := by
    intro g hg
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.1 hg
    exact hchain.1 V hV
  have hcardS : S.card = 2 * k + 1 := by
    rw [hS, Nat.card_Icc]; omega
  have hG : 2 ≤ (S \ τ.image (fun V : Sp F r => finrank F V)).card := by
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_image_of_injOn hinj, hcardS]
    omega
  obtain ⟨f₁, hf₁, f₂, hf₂, h12⟩ := Finset.one_lt_card.1 hG
  have key : ∀ f ∈ S \ τ.image (fun V : Sp F r => finrank F V),
      f ∈ S ∧ ∀ V ∈ τ, finrank F V ≠ f := by
    intro f hf
    rw [Finset.mem_sdiff, Finset.mem_image] at hf
    exact ⟨hf.1, fun V hV h => hf.2 ⟨V, hV, h⟩⟩
  have hFr : ∃ f₁ f₂ : ℕ, f₁ ≠ f₂ ∧ f₁ ∈ S ∧ f₂ ∈ S ∧ (∀ V ∈ τ, finrank F V ≠ f₁) ∧
      (∀ V ∈ τ, finrank F V ≠ f₂) :=
    ⟨f₁, f₂, h12, (key _ hf₁).1, (key _ hf₂).1, (key _ hf₁).2, (key _ hf₂).2⟩
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, ?_⟩
  · intro u v
    obtain ⟨A, hA, hAcp⟩ := vtx_cp hτ u
    obtain ⟨B, hB, hBcp⟩ := vtx_cp hτ v
    have hrg := rg_all hchain hE hFr A B hAcp hBcp
    have main : ∀ C : Sp F r, RG S τ A C → ∀ hC : Cp S τ C,
        (SteurerHDX.skeleton1 (SteurerHDX.link (flagsComplex F r k) τ)).Reachable u
          ⟨{C}, vtx_mem hτ hC⟩ := by
      intro C hAC
      induction hAC with
      | refl =>
        intro hC
        have : u = ⟨{A}, vtx_mem hτ hC⟩ := Subtype.ext hA
        rw [this]
      | @tail C₀ C₁ _ hstep ih =>
        intro hC₁
        obtain ⟨h0, h1, hne, hcmp⟩ := hstep
        refine (ih h0).trans (SimpleGraph.Adj.reachable ?_)
        refine ⟨?_, ?_⟩
        · intro h
          have := congrArg (fun s : SteurerHDX.faces (SteurerHDX.link (flagsComplex F r k) τ) 1 =>
            s.1) h
          exact hne (Finset.singleton_injective this)
        · apply pair_mem_link C₀ C₁ _ _ _
          · exact ((cp_iff hτ C₀).1 h0).1
          · exact ((cp_iff hτ C₁).1 h1).1
          · have hτ' : insert C₁ τ ∈ flagsComplex F r k := ((cp_iff hτ C₁).1 h1).2
            refine ((cp_iff hτ' C₀).1 ⟨h0.1, ?_, ?_⟩).2
            · intro V hV
              rcases Finset.mem_insert.1 hV with rfl | hV
              · intro hd
                exact hne (comp_eq_of_finrank hcmp hd.symm)
              · exact h0.2.1 V hV
            · intro V hV
              rcases Finset.mem_insert.1 hV with rfl | hV
              · exact hcmp
              · exact h0.2.2 V hV
    have := main B hrg hBcp
    have hv : v = ⟨{B}, vtx_mem hτ hBcp⟩ := Subtype.ext hB
    rw [hv]; exact this
  · obtain ⟨U, h1, h2, h3⟩ := exists_between (lo τ f₁) (hi τ f₁) f₁ (lo_le_hi hchain f₁)
        (finrank_lo_le hchain f₁) (le_finrank_hi hchain (hE f₁ (key _ hf₁).1))
    exact ⟨⟨{U}, vtx_mem hτ (cp_of_between hchain (key _ hf₁).1 (key _ hf₁).2 h3 h1 h2)⟩⟩

end Flags

section Spec
variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']

lemma symWalk_submatrix (f : ι' ≃ ι) (W : Matrix ι ι ℝ) :
    symWalk (W.submatrix f f) = (symWalk W).submatrix f f := by
  ext x y
  have hv : ∀ x, vdeg (W.submatrix f f) x = vdeg W (f x) := by
    intro x
    unfold vdeg
    simp only [Matrix.submatrix_apply]
    exact Equiv.sum_comp f (fun y => W (f x) y)
  simp [symWalk, hv]

lemma eig_one_eq {A : Matrix ι ι ℝ} {B : Matrix ι' ι' ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hc : A.charpoly = B.charpoly) (hA2 : 1 < Fintype.card ι) (hB2 : 1 < Fintype.card ι') :
    hA.eigenvalues₀ ⟨1, hA2⟩ = hB.eigenvalues₀ ⟨1, hB2⟩ := by
  have h1 := hA.sort_roots_charpoly_eq_eigenvalues₀
  have h2 := hB.sort_roots_charpoly_eq_eigenvalues₀
  rw [hc] at h1
  have h3 : List.ofFn hA.eigenvalues₀ = List.ofFn hB.eigenvalues₀ := h1.symm.trans h2
  have h4 := congrArg (fun l => l[1]?) h3
  simpa [List.getElem?_ofFn, hA2, hB2] using h4

lemma lambdaTwo_submatrix (f : ι' ≃ ι) (W : Matrix ι ι ℝ) :
    lambdaTwo (W.submatrix f f) = lambdaTwo W := by
  have hcard : Fintype.card ι' = Fintype.card ι := Fintype.card_congr f
  have hsw := symWalk_submatrix f W
  unfold lambdaTwo
  by_cases h : (symWalk W).IsHermitian ∧ 2 ≤ Fintype.card ι
  · have h' : (symWalk (W.submatrix f f)).IsHermitian ∧ 2 ≤ Fintype.card ι' := by
      refine ⟨?_, by omega⟩
      rw [hsw]; exact h.1.submatrix f
    rw [dif_pos h, dif_pos h']
    refine (eig_one_eq h.1 h'.1 ?_ (by omega) (by omega)).symm
    rw [hsw]
    have := Matrix.charpoly_reindex f.symm (symWalk W)
    simpa [Matrix.reindex_apply] using this.symm
  · have h' : ¬ ((symWalk (W.submatrix f f)).IsHermitian ∧ 2 ≤ Fintype.card ι') := by
      rintro ⟨h1, h2⟩
      apply h
      refine ⟨?_, by omega⟩
      have := h1.submatrix f.symm
      rw [hsw] at this
      simpa [Matrix.submatrix_submatrix] using this
    rw [dif_neg h, dif_neg h']
end Spec

section Map
variable {V : Type*} [DecidableEq V] (e : V ↪ ℕ)

/-- the transported complex -/
def mapX (X0 : Finset (Finset V)) : Finset (Finset ℕ) := X0.image (Finset.map e)

lemma mem_mapX {X0 : Finset (Finset V)} {σ' : Finset ℕ} :
    σ' ∈ mapX e X0 ↔ ∃ σ ∈ X0, σ.map e = σ' := by
  unfold mapX; rw [Finset.mem_image]

lemma map_mem_mapX {X0 : Finset (Finset V)} {σ : Finset V} (h : σ ∈ X0) :
    σ.map e ∈ mapX e X0 := (mem_mapX e).2 ⟨σ, h, rfl⟩

lemma isPure_mapX {X0 : Finset (Finset V)} {d : ℕ} (h : IsPure X0 d) : IsPure (mapX e X0) d := by
  refine ⟨?_, ?_⟩
  · intro τ' hτ' σ' hσ'
    obtain ⟨τ, hτ, rfl⟩ := (mem_mapX e).1 hτ'
    obtain ⟨u, hu, rfl⟩ := Finset.subset_map_iff.1 hσ'
    exact map_mem_mapX e (h.1 τ hτ u hu)
  · intro σ' hσ' hmax
    obtain ⟨σ, hσ, rfl⟩ := (mem_mapX e).1 hσ'
    rw [Finset.card_map]
    apply h.2 σ hσ
    intro ρ hρ hsub
    have := hmax (ρ.map e) (map_mem_mapX e hρ) (Finset.map_subset_map.2 hsub)
    exact Finset.map_injective e this

lemma faces_mapX (X0 : Finset (Finset V)) (i : ℕ) :
    SteurerHDX.faces (mapX e X0) i = (SteurerHDX.faces X0 i).image (Finset.map e) := by
  ext σ'
  unfold SteurerHDX.faces mapX
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨σ, hσ, rfl⟩, hc⟩
    exact ⟨σ, ⟨hσ, by simpa using hc⟩, rfl⟩
  · rintro ⟨σ, ⟨hσ, hc⟩, rfl⟩
    exact ⟨⟨σ, hσ, rfl⟩, by simpa using hc⟩

lemma card_faces_mapX (X0 : Finset (Finset V)) (i : ℕ) :
    (SteurerHDX.faces (mapX e X0) i).card = (SteurerHDX.faces X0 i).card := by
  rw [faces_mapX, Finset.card_image_of_injective _ (Finset.map_injective e)]

lemma isPartite_mapX {X0 : Finset (Finset V)} {d : ℕ} (hd : 0 < d) (h : IsPartite X0 d) :
    IsPartite (mapX e X0) d := by
  obtain ⟨c, hc⟩ := h
  refine ⟨Function.extend e c (fun _ => ⟨0, hd⟩), ?_⟩
  intro σ' hσ' i
  rw [faces_mapX, Finset.mem_image] at hσ'
  obtain ⟨σ, hσ, rfl⟩ := hσ'
  obtain ⟨y, ⟨hy1, hy2⟩, hy3⟩ := hc σ hσ i
  refine ⟨e y, ⟨(Finset.mem_map' e).2 hy1, ?_⟩, ?_⟩
  · rw [e.injective.extend_apply]; exact hy2
  · rintro x' ⟨hx1, hx2⟩
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.1 hx1
    rw [e.injective.extend_apply] at hx2
    rw [hy3 y' ⟨hy', hx2⟩]

lemma degree_mapX_le (X0 : Finset (Finset V)) (d : ℕ) :
    SteurerHDX.degree (mapX e X0) d ≤ SteurerHDX.degree X0 d := by
  unfold SteurerHDX.degree
  apply Finset.sup_le
  intro x' hx'
  rw [Finset.mem_biUnion] at hx'
  obtain ⟨σ', hσ', hx⟩ := hx'
  obtain ⟨σ, hσ, rfl⟩ := (mem_mapX e).1 hσ'
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 (by simpa using hx)
  have hxU : x ∈ X0.biUnion id := Finset.mem_biUnion.2 ⟨σ, hσ, by simpa using hx⟩
  refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun x => ((SteurerHDX.faces X0 d).filter
    (fun σ => x ∈ σ)).card) hxU)
  rw [faces_mapX, Finset.filter_image, Finset.card_image_of_injective _ (Finset.map_injective e)]
  congr 1
  apply Finset.filter_congr
  intro σ _
  exact Finset.mem_map' e


lemma mem_link_map {X0 : Finset (Finset V)} {τ : Finset V} {ρ' : Finset ℕ} :
    ρ' ∈ SteurerHDX.link (mapX e X0) (τ.map e) ↔ ∃ ρ ∈ SteurerHDX.link X0 τ, ρ.map e = ρ' := by
  unfold SteurerHDX.link
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨σ', ⟨hσ', hsub⟩, rfl⟩
    obtain ⟨σ, hσ, rfl⟩ := (mem_mapX e).1 hσ'
    exact ⟨σ \ τ, ⟨σ, ⟨hσ, Finset.map_subset_map.1 hsub⟩, rfl⟩, Finset.map_sdiff _ _⟩
  · rintro ⟨ρ, ⟨σ, ⟨hσ, hsub⟩, rfl⟩, rfl⟩
    exact ⟨σ.map e, ⟨map_mem_mapX e hσ, Finset.map_subset_map.2 hsub⟩, (Finset.map_sdiff _ _).symm⟩

/-- the vertex map on links -/
def linkMap (X0 : Finset (Finset V)) (τ : Finset V)
    (s : SteurerHDX.faces (SteurerHDX.link X0 τ) 1) :
    SteurerHDX.faces (SteurerHDX.link (mapX e X0) (τ.map e)) 1 :=
  ⟨s.1.map e, by
    have hs := s.2
    unfold SteurerHDX.faces at hs ⊢
    rw [Finset.mem_filter] at hs ⊢
    exact ⟨(mem_link_map e).2 ⟨s.1, hs.1, rfl⟩, by rw [Finset.card_map]; exact hs.2⟩⟩

lemma linkMap_bijective (X0 : Finset (Finset V)) (τ : Finset V) :
    Function.Bijective (linkMap e X0 τ) := by
  constructor
  · intro s t h
    have := congrArg Subtype.val h
    exact Subtype.ext (Finset.map_injective e this)
  · intro t
    have ht := t.2
    unfold SteurerHDX.faces at ht
    rw [Finset.mem_filter] at ht
    obtain ⟨ρ, hρ, hρt⟩ := (mem_link_map e).1 ht.1
    refine ⟨⟨ρ, ?_⟩, Subtype.ext hρt⟩
    unfold SteurerHDX.faces
    rw [Finset.mem_filter]
    exact ⟨hρ, by rw [← Finset.card_map e, hρt]; exact ht.2⟩

/-- the isomorphism of 1-skeleta of links -/
noncomputable def linkIso (X0 : Finset (Finset V)) (τ : Finset V) :
    SteurerHDX.skeleton1 (SteurerHDX.link X0 τ) ≃g
      SteurerHDX.skeleton1 (SteurerHDX.link (mapX e X0) (τ.map e)) where
  toEquiv := Equiv.ofBijective (linkMap e X0 τ) (linkMap_bijective e X0 τ)
  map_rel_iff' := by
    intro s t
    simp only [Equiv.ofBijective_apply, SteurerHDX.skeleton1]
    show (linkMap e X0 τ s ≠ linkMap e X0 τ t ∧ (linkMap e X0 τ s).1 ∪ (linkMap e X0 τ t).1 ∈ _) ↔ _
    have h1 : linkMap e X0 τ s ≠ linkMap e X0 τ t ↔ s ≠ t :=
      (linkMap_bijective e X0 τ).1.ne_iff
    have h2 : (linkMap e X0 τ s).1 ∪ (linkMap e X0 τ t).1 = (s.1 ∪ t.1).map e := by
      simp [linkMap, Finset.map_union]
    rw [h1, h2]
    show _ ↔ (s ≠ t ∧ s.1 ∪ t.1 ∈ _)
    constructor
    · rintro ⟨a, b⟩
      refine ⟨a, ?_⟩
      obtain ⟨ρ, hρ, h⟩ := (mem_link_map e).1 b
      rw [Finset.map_inj] at h; exact h ▸ hρ
    · rintro ⟨a, b⟩
      exact ⟨a, (mem_link_map e).2 ⟨_, b, rfl⟩⟩

lemma lambdaTau_mapX (X0 : Finset (Finset V)) (τ : Finset V) :
    SteurerHDX.lambdaTau (mapX e X0) (τ.map e) = SteurerHDX.lambdaTau X0 τ := by
  classical
  unfold SteurerHDX.lambdaTau
  set φ := linkIso e X0 τ with hφ
  have hmat : (SimpleGraph.adjMatrix ℝ (SteurerHDX.skeleton1
      (SteurerHDX.link (mapX e X0) (τ.map e)))) =
      (SimpleGraph.adjMatrix ℝ (SteurerHDX.skeleton1 (SteurerHDX.link X0 τ))).submatrix
        φ.symm.toEquiv φ.symm.toEquiv := by
    ext s t
    simp only [Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply]
    have : (SteurerHDX.skeleton1 (SteurerHDX.link X0 τ)).Adj (φ.symm s) (φ.symm t) ↔
        (SteurerHDX.skeleton1 (SteurerHDX.link (mapX e X0) (τ.map e))).Adj s t :=
      φ.symm.map_adj_iff
    simp [this]
  rw [hmat]
  exact lambdaTwo_submatrix _ _

end Map

section Extra
variable {V : Type*} [DecidableEq V] (e : V ↪ ℕ)

lemma isConnected_mapX {X0 : Finset (Finset V)} {d : ℕ} (h : IsConnectedComplex X0 d) :
    IsConnectedComplex (mapX e X0) d := by
  intro τ' hτ' hcard
  obtain ⟨τ, hτ, rfl⟩ := (mem_mapX e).1 hτ'
  rw [Finset.card_map] at hcard
  exact (linkIso e X0 τ).connected_iff.1 (h τ hτ hcard)

lemma isTopLink_mapX {X0 : Finset (Finset V)} {d : ℕ} {a : ℝ} (h : IsTopLinkExpander X0 d a) :
    IsTopLinkExpander (mapX e X0) d a := by
  intro τ' hτ' hc
  obtain ⟨τ, hτ, rfl⟩ := (mem_mapX e).1 hτ'
  rw [Finset.card_map] at hc
  rw [lambdaTau_mapX]
  exact h τ hτ hc

end Extra

lemma exists_facet {V : Type*} [DecidableEq V] {X : Finset (Finset V)} {d : ℕ} (h : IsPure X d)
    {s : Finset V} (hs : s ∈ X) : ∃ σ ∈ SteurerHDX.faces X d, s ⊆ σ := by
  obtain ⟨σ, hσ, hmax⟩ := Finset.exists_max_image (X.filter (fun t => s ⊆ t)) Finset.card
    ⟨s, Finset.mem_filter.2 ⟨hs, subset_rfl⟩⟩
  rw [Finset.mem_filter] at hσ
  refine ⟨σ, ?_, hσ.2⟩
  unfold SteurerHDX.faces
  rw [Finset.mem_filter]
  refine ⟨hσ.1, h.2 σ hσ.1 ?_⟩
  intro ρ hρ hsub
  have hρ' := hmax ρ (Finset.mem_filter.2 ⟨hρ, hσ.2.trans hsub⟩)
  exact (Finset.eq_of_subset_of_card_le hsub hρ').symm

section Extra2
variable {F : Type*} [Field F] [Fintype F] {r k : ℕ} [DecidableEq (Sp F r)]

lemma single_mem_flags (hk : 1 ≤ k) (hkr : k < r) (W : Sp F r) (hW : finrank F W = r) :
    ({W} : Finset (Sp F r)) ∈ flagsComplex F r k := by
  rw [mem_flags]
  refine ⟨?_, ?_⟩
  · intro V hV
    rw [Finset.mem_singleton] at hV
    subst hV
    rw [hW, Finset.mem_Icc]; omega
  · intro V hV V' hV'
    rw [Finset.mem_singleton] at hV hV'
    subst hV; subst hV'; exact Or.inl le_rfl

lemma two_faces (hk : 1 ≤ k) (hkr : k < r) (hpure : IsPure (flagsComplex F r k) (2 * k + 1)) :
    2 ≤ (SteurerHDX.faces (flagsComplex F r k) (2 * k + 1)).card := by
  have hdimE : finrank F (Fin (2 * r) → F) = 2 * r := Module.finrank_fin_fun F
  obtain ⟨W₁, -, -, hW₁⟩ := exists_between (⊥ : Sp F r) ⊤ r bot_le (by simp) (by
    rw [finrank_top, hdimE]; omega)
  obtain ⟨H, -, hH2, hH3⟩ := exists_between (⊥ : Sp F r) W₁ (r - 1) bot_le (by simp) (by omega)
  have hne : W₁ ≠ ⊤ := by
    intro h
    rw [h, finrank_top, hdimE] at hW₁
    omega
  obtain ⟨x, hx⟩ : ∃ x, x ∉ W₁ := by
    by_contra hcon
    push_neg at hcon
    exact hne (eq_top_iff.2 (fun x _ => hcon x))
  have hxH : x ∉ H := fun h => hx (hH2 h)
  have hW₂ : finrank F (H ⊔ Submodule.span F {x} : Submodule F (Fin (2 * r) → F)) = r := by
    rw [finrank_sup_span_of_not_mem H x hxH, hH3]; omega
  obtain ⟨σ₁, hσ₁, hs₁⟩ := exists_facet hpure (single_mem_flags hk hkr W₁ hW₁)
  obtain ⟨σ₂, hσ₂, hs₂⟩ := exists_facet hpure
    (single_mem_flags hk hkr (H ⊔ Submodule.span F {x}) hW₂)
  have hne12 : σ₁ ≠ σ₂ := by
    intro h
    subst h
    have hch := (mem_flags.1 (Finset.mem_filter.1 hσ₁).1).2
    have h1 : W₁ ∈ σ₁ := hs₁ (Finset.mem_singleton_self _)
    have h2 : (H ⊔ Submodule.span F {x} : Sp F r) ∈ σ₁ := hs₂ (Finset.mem_singleton_self _)
    have := comp_eq_of_finrank (hch _ h1 _ h2) (by rw [hW₁, hW₂])
    apply hx
    rw [this]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  exact Finset.one_lt_card.2 ⟨σ₁, hσ₁, σ₂, hσ₂, hne12⟩

end Extra2

end SteurerHDX.Dev.T24

namespace SteurerHDX

theorem chk_theorem_2_4 :
    ∃ c₁ c₂ C : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < C ∧
    ∀ k r q : ℕ, 1 ≤ k → k < r → IsPrimePow q → (4 * (2 * k + 1) + 1) ^ 2 ≤ q →
    ∃ X : Finset (Finset ℕ),
      IsPure X (2 * k + 1) ∧ IsPartite X (2 * k + 1) ∧ 2 ≤ (faces X (2 * k + 1)).card ∧
      (q : ℝ) ^ (c₁ * (r : ℝ) ^ 2) ≤ ((faces X 1).card : ℝ) ∧
      ((faces X 1).card : ℝ) ≤ (q : ℝ) ^ (c₂ * (r : ℝ) ^ 2) ∧
      (degree X (2 * k + 1) : ℝ) ≤ (q : ℝ) ^ (C * r * (2 * k + 1)) ∧
      IsTopLinkExpander X (2 * k + 1) (1 / (2 * (2 * k + 1))) ∧
      lambdaTwo (downUp X (2 * k + 1)) ≤ 1 - 1 / (Real.exp 1 * (2 * k + 1)) := by
  classical
  obtain ⟨c₀, c₁, c₂, C, h0, h1, h2, hC, hfl⟩ := section_2_3_flags
  refine ⟨c₁, c₂, C, h1, h2, hC, ?_⟩
  intro k r q hk hkr hq hqd
  obtain ⟨p, n, hp, hn, hpq⟩ := hq
  haveI : Fact (Nat.Prime p) := ⟨Nat.prime_iff.2 hp⟩
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p n) = q := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p n hn.ne']; exact hpq
  obtain ⟨hpure, hpart, -, -, hc1, hc2, hdeg, hexp⟩ := hfl (GaloisField p n) r k hk hkr
  haveI : Finite (Dev.T24.Sp (GaloisField p n) r) :=
    Finite.of_injective (fun W : Dev.T24.Sp (GaloisField p n) r => (W : Set (Fin (2 * r) → GaloisField p n)))
      SetLike.coe_injective
  obtain ⟨f, hf⟩ := exists_injective_nat (Dev.T24.Sp (GaloisField p n) r)
  let e : Dev.T24.Sp (GaloisField p n) r ↪ ℕ := ⟨f, hf⟩
  set X0 := flagsComplex (GaloisField p n) r k with hX0
  have hq' : (q : ℝ) = (Fintype.card (GaloisField p n) : ℝ) := by rw [hcard]
  have hd0 : 0 < 2 * k + 1 := by omega
  have hqd' : (4 * ((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2 ≤ (q : ℝ) := by
    exact_mod_cast hqd
  have hsq : 4 * ((2 * k + 1 : ℕ) : ℝ) + 1 ≤ Real.sqrt (q : ℝ) :=
    Real.le_sqrt_of_sq_le hqd'
  have hdpos : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by exact_mod_cast hd0
  have hTL0 : IsTopLinkExpander X0 (2 * k + 1) (1 / (2 * ((2 * k + 1 : ℕ) : ℝ))) := by
    intro τ hτ hc
    refine (hexp τ hτ hc).trans ?_
    rw [hcard]
    have h4 : (4 * ((2 * k + 1 : ℕ) : ℝ)) ≤ Real.sqrt (q : ℝ) - 1 := by linarith
    calc 2 / (Real.sqrt (q : ℝ) - 1) ≤ 2 / (4 * ((2 * k + 1 : ℕ) : ℝ)) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) h4
      _ = 1 / (2 * ((2 * k + 1 : ℕ) : ℝ)) := by field_simp; ring
  have hTL := Dev.T24.isTopLink_mapX e hTL0
  have hpureX := Dev.T24.isPure_mapX e hpure
  have hfaces := Dev.T24.two_faces hk hkr hpure
  have hconn := Dev.T24.isConnected_mapX e (Dev.T24.flags_connected hk hkr)
  have hexp' : IsTopLinkExpander (Dev.T24.mapX e X0) (2 * k + 1)
      ((1 - 1 / 2) / ((2 * k + 1 : ℕ) : ℝ)) := by
    have : ((1 : ℝ) - 1 / 2) / ((2 * k + 1 : ℕ) : ℝ) = 1 / (2 * ((2 * k + 1 : ℕ) : ℝ)) := by
      field_simp; ring
    rw [this]; exact hTL
  have hcardX : 2 ≤ (faces (Dev.T24.mapX e X0) (2 * k + 1)).card := by
    rw [Dev.T24.card_faces_mapX]; exact hfaces
  obtain ⟨-, hb⟩ := theorem_2_3 (Dev.T24.mapX e X0) (2 * k + 1) (1 / 2) hpureX hconn hcardX
    (by norm_num) (by norm_num) hexp'
  have hb' := hb rfl
  have hsg : spectralGap (downUp (Dev.T24.mapX e X0) (2 * k + 1)) =
      1 - lambdaTwo (downUp (Dev.T24.mapX e X0) (2 * k + 1)) := rfl
  refine ⟨Dev.T24.mapX e X0, hpureX, Dev.T24.isPartite_mapX e hd0 hpart, hcardX, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Dev.T24.card_faces_mapX, hq']; exact hc1
  · rw [Dev.T24.card_faces_mapX, hq']; exact hc2
  · rw [hq']
    refine le_trans (Nat.cast_le.2 (Dev.T24.degree_mapX_le e X0 _)) (hdeg.trans ?_)
    have hone : (1 : ℝ) ≤ (Fintype.card (GaloisField p n) : ℝ) := by
      exact_mod_cast Fintype.card_pos
    apply Real.rpow_le_rpow_of_exponent_le hone
    have : (0 : ℝ) ≤ C * k * r := by positivity
    have hk' : (0 : ℝ) ≤ C * r * (k + 1) := by positivity
    nlinarith
  · have : (1 : ℝ) / (2 * (2 * k + 1)) = 1 / (2 * ((2 * k + 1 : ℕ) : ℝ)) := by push_cast; ring
    rw [this]; exact hTL
  · have : (1 : ℝ) / (Real.exp 1 * (2 * k + 1)) = 1 / (Real.exp 1 * ((2 * k + 1 : ℕ) : ℝ)) := by
      push_cast; ring
    rw [this]; linarith

end SteurerHDX
end

theorem solution : type_of% @SteurerHDX.chk_theorem_2_4 := @SteurerHDX.chk_theorem_2_4
