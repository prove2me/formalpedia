-- Prove2me | solution 1 for Ziegler2002.zp_tucker
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T10:09:45.642668+00:00
-- url     : https://prove2.me/submissions/c4aee45f-a856-47a0-b31f-f80b912e6b1d

import Mathlib

section
set_option autoImplicit false

/-!
Chains indexed by lists: `Ch α` is the free abelian group on `List α`, with the augmented
boundary `bd`, the cone `cons x`, the push-forward `mp f`, and the prism operator `P g`.
-/

namespace Ziegler2002.Dev

open Finsupp

abbrev Ch (α : Type*) := List α →₀ ℤ

section generic

variable {α β γ : Type*}

theorem hom_ext {M : Type*} [AddCommGroup M] (f g : Ch α →ₗ[ℤ] M)
    (h : ∀ l, f (single l 1) = g (single l 1)) : f = g := by
  refine Finsupp.lhom_ext fun l r => ?_
  rw [← Finsupp.smul_single_one, map_smul, map_smul, h]

theorem map_supported {M : Type*} [AddCommGroup M] (F : Ch α →ₗ[ℤ] M) (S : Submodule ℤ M)
    (s : Set (List α)) (h : ∀ l ∈ s, F (single l 1) ∈ S) :
    ∀ c ∈ Finsupp.supported ℤ ℤ s, F c ∈ S := by
  intro c hc
  have hc' := (Finsupp.mem_supported ℤ c).1 hc
  have h1 : F c = ∑ l ∈ c.support, F (single l (c l)) := by
    conv_lhs => rw [← Finsupp.sum_single c]
    rw [Finsupp.sum, map_sum]
  rw [h1]
  refine Submodule.sum_mem _ fun l hl => ?_
  rw [← Finsupp.smul_single_one, map_smul]
  exact S.smul_mem _ (h l (hc' hl))

theorem eq_on_supported {M : Type*} [AddCommGroup M] (F G : Ch α →ₗ[ℤ] M)
    (s : Set (List α)) (h : ∀ l ∈ s, F (single l 1) = G (single l 1)) :
    ∀ c ∈ Finsupp.supported ℤ ℤ s, F c = G c := by
  intro c hc
  have := map_supported (F - G) ⊥ s (fun l hl => by simp [h l hl]) c hc
  simpa [sub_eq_zero] using this

/-- prepend a letter -/
noncomputable def cons (x : α) : Ch α →ₗ[ℤ] Ch α := Finsupp.lmapDomain ℤ ℤ (List.cons x)

@[simp] theorem cons_single (x : α) (l : List α) (r : ℤ) :
    cons x (single l r) = single (x :: l) r := by
  simp [cons]

/-- push forward along a map of letters -/
noncomputable def mp (f : α → β) : Ch α →ₗ[ℤ] Ch β := Finsupp.lmapDomain ℤ ℤ (List.map f)

@[simp] theorem mp_single (f : α → β) (l : List α) (r : ℤ) :
    mp f (single l r) = single (l.map f) r := by
  simp [mp]

theorem mp_cons (f : α → β) (x : α) (c : Ch α) : mp f (cons x c) = cons (f x) (mp f c) := by
  have : (mp f) ∘ₗ (cons x) = (cons (f x)) ∘ₗ (mp f) := hom_ext _ _ fun l => by simp
  exact LinearMap.congr_fun this c

theorem mp_mp (f : α → β) (g : β → γ) (c : Ch α) : mp g (mp f c) = mp (g ∘ f) c := by
  have : (mp g) ∘ₗ (mp f) = mp (g ∘ f) := hom_ext _ _ fun l => by simp
  exact LinearMap.congr_fun this c

theorem mp_id (c : Ch α) : mp (id : α → α) c = c := by
  have : mp (id : α → α) = LinearMap.id := hom_ext _ _ fun l => by simp
  exact LinearMap.congr_fun this c

theorem mp_apply_nil (f : α → β) (c : Ch α) : (mp f c) [] = c [] := by
  have : (Finsupp.lapply ([] : List β)) ∘ₗ (mp f) = Finsupp.lapply ([] : List α) :=
    hom_ext _ _ fun l => by
      cases l <;> simp [Finsupp.single_apply]
  exact LinearMap.congr_fun this c

/-- boundary of a list (augmented: the boundary of a one-letter list is the empty list) -/
noncomputable def bdL : List α → Ch α
  | [] => 0
  | x :: l => single l 1 - cons x (bdL l)

noncomputable def bd : Ch α →ₗ[ℤ] Ch α := Finsupp.linearCombination ℤ bdL

@[simp] theorem bd_single_one (l : List α) : bd (single l 1) = bdL l := by
  simp [bd, Finsupp.linearCombination_single]

theorem bd_cons (x : α) (c : Ch α) : bd (cons x c) = c - cons x (bd c) := by
  have : (bd) ∘ₗ (cons x) = LinearMap.id - (cons x) ∘ₗ bd := hom_ext _ _ fun l => by
    simp [bdL]
  exact LinearMap.congr_fun this c

theorem bd_bd (c : Ch α) : bd (bd c) = 0 := by
  have : (bd : Ch α →ₗ[ℤ] Ch α) ∘ₗ bd = 0 := hom_ext _ _ fun l => by
    induction l with
    | nil => simp [bdL]
    | cons x l ih =>
      have ih' : bd (bdL l) = 0 := by simpa using ih
      simp [bdL, bd_cons, ih']
  exact LinearMap.congr_fun this c

theorem bdL_map (f : α → β) (l : List α) : bdL (l.map f) = mp f (bdL l) := by
  induction l with
  | nil => simp [bdL]
  | cons x l ih => simp [bdL, ih, mp_cons]

theorem bd_mp (f : α → β) (c : Ch α) : bd (mp f c) = mp f (bd c) := by
  have : (bd) ∘ₗ (mp f) = (mp f) ∘ₗ bd := hom_ext _ _ fun l => by
    simp [bdL_map]
  exact LinearMap.congr_fun this c

/-- prism operator for a self-map `g` -/
noncomputable def PL (g : α → α) : List α → Ch α
  | [] => 0
  | x :: l => cons x (single ((x :: l).map g) 1 - PL g l)

noncomputable def P (g : α → α) : Ch α →ₗ[ℤ] Ch α := Finsupp.linearCombination ℤ (PL g)

@[simp] theorem P_single_one (g : α → α) (l : List α) : P g (single l 1) = PL g l := by
  simp [P, Finsupp.linearCombination_single]

theorem P_cons (g : α → α) (x : α) (c : Ch α) :
    P g (cons x c) = cons x (mp g (cons x c) - P g c) := by
  have : (P g) ∘ₗ (cons x) = (cons x) ∘ₗ ((mp g) ∘ₗ (cons x) - P g) := hom_ext _ _ fun l => by
    simp [PL]
  exact LinearMap.congr_fun this c

theorem prism (g : α → α) (c : Ch α) : bd (P g c) + P g (bd c) = mp g c - c := by
  have : (bd) ∘ₗ (P g) + (P g) ∘ₗ bd = mp g - LinearMap.id := hom_ext _ _ fun l => by
    induction l with
    | nil => simp [PL, bdL]
    | cons x l ih =>
      have ih' : bd (PL g l) + P g (bdL l) = single (l.map g) 1 - single l 1 := by
        simpa using ih
      have e1 : bd (PL g l) = single (l.map g) 1 - single l 1 - P g (bdL l) := by
        rw [← ih']; abel
      simp only [LinearMap.add_apply, LinearMap.comp_apply, P_single_one, bd_single_one,
        LinearMap.sub_apply, LinearMap.id_apply, mp_single, PL, bdL, map_sub, bd_cons, P_cons,
        mp_cons, cons_single, bdL_map, List.map_cons, e1]
      abel
  exact LinearMap.congr_fun this c

/-- filling: cone from `e` over the `g`-image, minus the prism -/
noncomputable def fill (e : α) (g : α → α) (z : Ch α) : Ch α := cons e (mp g z) - P g z

theorem bd_fill (e : α) (g : α → α) (z : Ch α) (hz : bd z = 0) : bd (fill e g z) = z := by
  have h := prism g z
  rw [hz, map_zero, add_zero] at h
  simp [fill, bd_cons, bd_mp, hz, h]

end generic

end Ziegler2002.Dev
end

section
set_option autoImplicit false

namespace Ziegler2002.Dev

open Finsupp

section cyc

variable {G : Type*} [Fintype G] [AddCommGroup G] {α β : Type*}

/-- the norm operator of a family of letter maps -/
noncomputable def Nop (σ : G → α → α) : Ch α →ₗ[ℤ] Ch α := ∑ g, mp (σ g)

theorem Nop_apply (σ : G → α → α) (c : Ch α) : Nop σ c = ∑ g, mp (σ g) c := by
  simp [Nop, LinearMap.sum_apply]

/-- `1 - ω` in odd degrees, the norm in even degrees -/
noncomputable def tau (u : G) (σ : G → α → α) (j : ℕ) : Ch α →ₗ[ℤ] Ch α :=
  if j % 2 = 1 then LinearMap.id - mp (σ u) else Nop σ

theorem tau_odd (u : G) (σ : G → α → α) (j : ℕ) (hj : j % 2 = 1) (c : Ch α) :
    tau u σ j c = c - mp (σ u) c := by
  simp [tau, hj]

theorem tau_even (u : G) (σ : G → α → α) (j : ℕ) (hj : j % 2 = 0) (c : Ch α) :
    tau u σ j c = Nop σ c := by
  simp [tau, hj]

theorem Nop_one_sub (u : G) (σ : G → α → α) (hσ : ∀ g, σ g ∘ σ u = σ (g + u)) (c : Ch α) :
    Nop σ (c - mp (σ u) c) = 0 := by
  rw [map_sub, Nop_apply, Nop_apply, sub_eq_zero]
  simp only [mp_mp, hσ]
  exact (Equiv.sum_comp (Equiv.addRight u) (fun g => mp (σ g) c)).symm

theorem one_sub_Nop (u : G) (σ : G → α → α) (hσ : ∀ g, σ u ∘ σ g = σ (g + u)) (c : Ch α) :
    Nop σ c - mp (σ u) (Nop σ c) = 0 := by
  rw [Nop_apply, map_sum, sub_eq_zero]
  simp only [mp_mp, hσ]
  exact (Equiv.sum_comp (Equiv.addRight u) (fun g => mp (σ g) c)).symm

theorem tau_tau (u : G) (σ : G → α → α) (hσ : ∀ g, σ g ∘ σ u = σ (g + u))
    (hσ' : ∀ g, σ u ∘ σ g = σ (g + u)) (j : ℕ) (c : Ch α) :
    tau u σ (j + 1) (tau u σ j c) = 0 := by
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · rw [tau_odd u σ (j + 1) (by omega), tau_even u σ j hj]
    exact one_sub_Nop u σ hσ' c
  · rw [tau_even u σ (j + 1) (by omega), tau_odd u σ j hj]
    exact Nop_one_sub u σ hσ c

theorem bd_tau (u : G) (σ : G → α → α) (j : ℕ) (c : Ch α) :
    bd (tau u σ j c) = tau u σ j (bd c) := by
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · rw [tau_even u σ j hj, tau_even u σ j hj, Nop_apply, Nop_apply, map_sum]
    simp only [bd_mp]
  · rw [tau_odd u σ j hj, tau_odd u σ j hj, map_sub, bd_mp]

theorem tau_mem_supported (u : G) (σ : G → α → α) (s : Set (List α))
    (hs : ∀ l ∈ s, ∀ g, l.map (σ g) ∈ s) (j : ℕ) (c : Ch α)
    (hc : c ∈ Finsupp.supported ℤ ℤ s) : tau u σ j c ∈ Finsupp.supported ℤ ℤ s := by
  have hmp : ∀ g, mp (σ g) c ∈ Finsupp.supported ℤ ℤ s := fun g =>
    map_supported (mp (σ g)) _ s (fun l hl => by
      rw [mp_single]; exact Finsupp.single_mem_supported ℤ _ (hs l hl g)) c hc
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · rw [tau_even u σ j hj, Nop_apply]
    exact Submodule.sum_mem _ fun g _ => hmp g
  · rw [tau_odd u σ j hj]
    exact Submodule.sub_mem _ hc (hmp u)

theorem mp_tau (u : G) (σ : G → α → α) (σ' : G → β → β) (f : α → β) (s : Set (List α))
    (hs : ∀ l ∈ s, ∀ x ∈ l, ∀ g, f (σ g x) = σ' g (f x)) (j : ℕ) (c : Ch α)
    (hc : c ∈ Finsupp.supported ℤ ℤ s) : mp f (tau u σ j c) = tau u σ' j (mp f c) := by
  have hmp : ∀ g, mp f (mp (σ g) c) = mp (σ' g) (mp f c) := fun g =>
    eq_on_supported ((mp f) ∘ₗ (mp (σ g))) ((mp (σ' g)) ∘ₗ (mp f)) s (fun l hl => by
      simp only [LinearMap.comp_apply, mp_single, List.map_map]
      congr 1
      exact List.map_congr_left fun x hx => hs l hl x hx g) c hc
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · rw [tau_even u σ j hj, tau_even u σ' j hj, Nop_apply, Nop_apply, map_sum]
    simp only [hmp]
  · rw [tau_odd u σ j hj, tau_odd u σ' j hj, map_sub, hmp]

end cyc

end Ziegler2002.Dev
end

section
set_option autoImplicit false

namespace Ziegler2002.Dev

open Finsupp

section dmod

variable {α β : Type*}

theorem all_mem {M : Type*} [AddCommGroup M] (F : Ch α →ₗ[ℤ] M) (S : Submodule ℤ M)
    (h : ∀ l, F (single l 1) ∈ S) (c : Ch α) : F c ∈ S :=
  map_supported F S Set.univ (fun l _ => h l) c (by simp [Finsupp.supported_univ])

/-- generators of the alternation relations: a list with two equal adjacent letters, and
the sum of two lists differing by an adjacent transposition -/
def Dgen (α : Type*) : Set (Ch α) :=
  {c | (∃ l₁ a l₂, c = single (l₁ ++ a :: a :: l₂) 1) ∨
    ∃ l₁ a b l₂, c = single (l₁ ++ a :: b :: l₂) 1 + single (l₁ ++ b :: a :: l₂) 1}

noncomputable def D (α : Type*) : Submodule ℤ (Ch α) := Submodule.span ℤ (Dgen α)

theorem D_map {γ : Type*} (F : Ch α →ₗ[ℤ] Ch γ) (h : ∀ c ∈ Dgen α, F c ∈ D γ) :
    ∀ d ∈ D α, F d ∈ D γ := by
  have : D α ≤ (D γ).comap F := Submodule.span_le.2 fun c hc => h c hc
  exact fun d hd => this hd

theorem cons_mem_D (x : α) (d : Ch α) (hd : d ∈ D α) : cons x d ∈ D α := by
  refine D_map (cons x) ?_ d hd
  rintro c (⟨l₁, a, l₂, rfl⟩ | ⟨l₁, a, b, l₂, rfl⟩)
  · rw [cons_single]
    exact Submodule.subset_span (Or.inl ⟨x :: l₁, a, l₂, rfl⟩)
  · rw [map_add, cons_single, cons_single]
    exact Submodule.subset_span (Or.inr ⟨x :: l₁, a, b, l₂, rfl⟩)

theorem mp_mem_D (f : α → β) (d : Ch α) (hd : d ∈ D α) : mp f d ∈ D β := by
  refine D_map (mp f) ?_ d hd
  rintro c (⟨l₁, a, l₂, rfl⟩ | ⟨l₁, a, b, l₂, rfl⟩)
  · rw [mp_single]
    exact Submodule.subset_span (Or.inl ⟨l₁.map f, f a, l₂.map f, by simp⟩)
  · rw [map_add, mp_single, mp_single]
    exact Submodule.subset_span (Or.inr ⟨l₁.map f, f a, f b, l₂.map f, by simp⟩)

theorem bdL_rep_mem_D (a : α) (l₂ : List α) :
    ∀ l₁ : List α, bdL (l₁ ++ a :: a :: l₂) ∈ D α := by
  intro l₁
  induction l₁ with
  | nil =>
    have e : bdL ([] ++ a :: a :: l₂) = ((cons a) ∘ₗ (cons a)) (bdL l₂) := by
      simp [bdL]
    rw [e]
    refine all_mem _ _ (fun l => ?_) _
    simp only [LinearMap.comp_apply, cons_single]
    exact Submodule.subset_span (Or.inl ⟨[], a, l, rfl⟩)
  | cons x l₁ ih =>
    have e : bdL (x :: l₁ ++ a :: a :: l₂)
        = single (l₁ ++ a :: a :: l₂) 1 - cons x (bdL (l₁ ++ a :: a :: l₂)) := rfl
    rw [e]
    exact Submodule.sub_mem _ (Submodule.subset_span (Or.inl ⟨l₁, a, l₂, rfl⟩))
      (cons_mem_D x _ ih)

theorem bdL_swap_mem_D (a b : α) (l₂ : List α) :
    ∀ l₁ : List α, bdL (l₁ ++ a :: b :: l₂) + bdL (l₁ ++ b :: a :: l₂) ∈ D α := by
  intro l₁
  induction l₁ with
  | nil =>
    have e : bdL ([] ++ a :: b :: l₂) + bdL ([] ++ b :: a :: l₂)
        = ((cons a) ∘ₗ (cons b) + (cons b) ∘ₗ (cons a)) (bdL l₂) := by
      simp [bdL]
      abel
    rw [e]
    refine all_mem _ _ (fun l => ?_) _
    simp only [LinearMap.add_apply, LinearMap.comp_apply, cons_single]
    exact Submodule.subset_span (Or.inr ⟨[], a, b, l, rfl⟩)
  | cons x l₁ ih =>
    have e : bdL (x :: l₁ ++ a :: b :: l₂) + bdL (x :: l₁ ++ b :: a :: l₂)
        = (single (l₁ ++ a :: b :: l₂) 1 + single (l₁ ++ b :: a :: l₂) 1)
          - cons x (bdL (l₁ ++ a :: b :: l₂) + bdL (l₁ ++ b :: a :: l₂)) := by
      simp only [List.cons_append, bdL, map_add]
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.subset_span (Or.inr ⟨l₁, a, b, l₂, rfl⟩))
      (cons_mem_D x _ ih)

theorem bd_mem_D (d : Ch α) (hd : d ∈ D α) : bd d ∈ D α := by
  refine D_map bd ?_ d hd
  rintro c (⟨l₁, a, l₂, rfl⟩ | ⟨l₁, a, b, l₂, rfl⟩)
  · rw [bd_single_one]
    exact bdL_rep_mem_D a l₂ l₁
  · rw [map_add, bd_single_one, bd_single_one]
    exact bdL_swap_mem_D a b l₂ l₁

theorem apply_nil_of_mem_D (d : Ch α) (hd : d ∈ D α) : d [] = 0 := by
  have : D α ≤ LinearMap.ker (Finsupp.lapply ([] : List α)) := by
    refine Submodule.span_le.2 ?_
    rintro c (⟨l₁, a, l₂, rfl⟩ | ⟨l₁, a, b, l₂, rfl⟩)
    · simp
    · simp
  exact this hd

theorem dup_mem_D (a : α) (l₃ : List α) :
    ∀ l₂ l₁ : List α, single (l₁ ++ a :: (l₂ ++ a :: l₃)) (1 : ℤ) ∈ D α := by
  intro l₂
  induction l₂ with
  | nil =>
    intro l₁
    exact Submodule.subset_span (Or.inl ⟨l₁, a, l₃, rfl⟩)
  | cons b l₂ ih =>
    intro l₁
    have h1 : single (l₁ ++ a :: b :: (l₂ ++ a :: l₃)) (1 : ℤ)
        + single (l₁ ++ b :: a :: (l₂ ++ a :: l₃)) 1 ∈ D α :=
      Submodule.subset_span (Or.inr ⟨l₁, a, b, _, rfl⟩)
    have h2 := ih (l₁ ++ [b])
    have e : l₁ ++ [b] ++ a :: (l₂ ++ a :: l₃) = l₁ ++ b :: a :: (l₂ ++ a :: l₃) := by simp
    rw [e] at h2
    have := Submodule.sub_mem _ h1 h2
    simpa using this

theorem exists_dup_of_not_nodup :
    ∀ l : List α, ¬ l.Nodup → ∃ l₁ a l₂ l₃, l = l₁ ++ a :: (l₂ ++ a :: l₃) := by
  intro l
  induction l with
  | nil => intro h; exact absurd List.nodup_nil h
  | cons x l ih =>
    intro h
    by_cases hx : x ∈ l
    · obtain ⟨s, t, rfl⟩ := List.append_of_mem hx
      exact ⟨[], x, s, t, rfl⟩
    · have hl : ¬ l.Nodup := fun hl => h (List.nodup_cons.2 ⟨hx, hl⟩)
      obtain ⟨l₁, a, l₂, l₃, rfl⟩ := ih hl
      exact ⟨x :: l₁, a, l₂, l₃, rfl⟩

theorem single_mem_D_of_not_nodup (l : List α) (h : ¬ l.Nodup) : single l (1 : ℤ) ∈ D α := by
  obtain ⟨l₁, a, l₂, l₃, rfl⟩ := exists_dup_of_not_nodup l h
  exact dup_mem_D a l₃ l₂ l₁

theorem bdL_mem_supported (l : List α) :
    bdL l ∈ Finsupp.supported ℤ ℤ {l' : List α | (∀ y ∈ l', y ∈ l) ∧ l'.length + 1 = l.length} := by
  induction l with
  | nil => simp [bdL]
  | cons x l ih =>
    refine Submodule.sub_mem _ (Finsupp.single_mem_supported ℤ _ ?_) ?_
    · exact ⟨fun y hy => List.mem_cons_of_mem _ hy, rfl⟩
    · refine map_supported (cons x) _ _ (fun l' hl' => ?_) _ ih
      rw [cons_single]
      refine Finsupp.single_mem_supported ℤ _ ⟨?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hl'.1 y hy)
      · simp [hl'.2]

end dmod

end Ziegler2002.Dev
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Ziegler2002.Dev

open Finsupp
open scoped Classical

section target

variable {q m : ℕ}

/-- labels -/
abbrev Lab (q m : ℕ) := ZMod (q + 1) × Fin m

def sY (g : ZMod (q + 1)) (y : Lab q m) : Lab q m := (y.1 + g, y.2)

theorem sY_comp' (g u : ZMod (q + 1)) : (sY u : Lab q m → Lab q m) ∘ sY g = sY (g + u) := by
  funext y
  simp only [sY, Function.comp_apply, Prod.mk.injEq, and_true]
  ring

theorem sY_zero : (sY 0 : Lab q m → Lab q m) = id := by
  funext y
  simp [sY]

/-- no full fibre -/
def NF (l : List (Lab q m)) : Prop := ¬ ∃ t : Fin m, ∀ a : ZMod (q + 1), (a, t) ∈ l

theorem NF_mono {l l' : List (Lab q m)} (h : ∀ y ∈ l', y ∈ l) (hl : NF l) : NF l' :=
  fun ⟨t, ht⟩ => hl ⟨t, fun a => h _ (ht a)⟩

theorem NF_map (g : ZMod (q + 1)) {l : List (Lab q m)} (hl : NF l) : NF (l.map (sY g)) := by
  rintro ⟨t, ht⟩
  refine hl ⟨t, fun a => ?_⟩
  obtain ⟨y, hy, e⟩ := List.mem_map.1 (ht (a + g))
  have : y = (a, t) := by
    simp only [sY, Prod.mk.injEq, add_left_inj] at e
    exact Prod.ext e.1 e.2
  rw [← this]; exact hy

noncomputable def ML (q m r : ℕ) : Submodule ℤ (Ch (Lab q m)) :=
  Finsupp.supported ℤ ℤ {l | NF l ∧ r ≤ l.length}

theorem mp_sY_mem_ML (g : ZMod (q + 1)) (r : ℕ) (c : Ch (Lab q m)) (hc : c ∈ ML q m r) :
    mp (sY g) c ∈ ML q m r := by
  refine map_supported (mp (sY g)) _ _ (fun l hl => ?_) c hc
  rw [mp_single]
  exact Finsupp.single_mem_supported ℤ _ ⟨NF_map g hl.1, by simpa using hl.2⟩

theorem bd_mem_ML (r : ℕ) (c : Ch (Lab q m)) (hc : c ∈ ML q m (r + 1)) : bd c ∈ ML q m r := by
  refine map_supported bd _ _ (fun l hl => ?_) c hc
  rw [bd_single_one]
  refine Finsupp.supported_mono ?_ (bdL_mem_supported l)
  rintro l' ⟨h1, h2⟩
  exact ⟨NF_mono h1 hl.1, by have := hl.2; omega⟩

theorem card_le_of_NF (l : List (Lab q m)) (hl : NF l) (hnd : l.Nodup) : l.length ≤ q * m := by
  rw [← List.toFinset_card_of_nodup hnd]
  have h1 := Finset.card_le_mul_card_image (f := Prod.snd) l.toFinset q (by
    intro t _
    obtain ⟨a, ha⟩ := not_forall.1 (fun h => hl ⟨t, h⟩)
    have hsub : (l.toFinset.filter (fun x => x.2 = t)).image Prod.fst
        ⊆ (Finset.univ : Finset (ZMod (q + 1))).erase a := by
      intro b hb
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
      rw [Finset.mem_filter, List.mem_toFinset] at hy
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      exact ha (by rw [← hy.2]; exact hy.1)
    have hinj : Set.InjOn Prod.fst (l.toFinset.filter (fun x : Lab q m => x.2 = t) : Set (Lab q m)) := by
      intro y hy y' hy' e
      rw [Finset.mem_coe, Finset.mem_filter] at hy hy'
      exact Prod.ext e (hy.2.trans hy'.2.symm)
    rw [← Finset.card_image_of_injOn hinj]
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card] at this
    simpa using this)
  have h2 : (l.toFinset.image Prod.snd).card ≤ m := by
    have := Finset.card_le_univ (l.toFinset.image Prod.snd)
    simpa using this
  calc l.toFinset.card ≤ q * (l.toFinset.image Prod.snd).card := h1
    _ ≤ q * m := Nat.mul_le_mul_left _ h2

/-! ### the phase -/

noncomputable def t0 (l : List (Lab q m)) : ℕ := sInf {t | ∃ y ∈ l, y.2.val = t}

noncomputable def Aset (l : List (Lab q m)) : Finset (ZMod (q + 1)) :=
  Finset.univ.filter (fun a => ∃ y ∈ l, y.1 = a ∧ y.2.val = t0 l)

noncomputable def phase (l : List (Lab q m)) : ZMod (q + 1) :=
  (∑ a ∈ Aset l, a) * ((Aset l).card : ZMod (q + 1))⁻¹

theorem t0_congr {l l' : List (Lab q m)} (h : ∀ y, y ∈ l ↔ y ∈ l') : t0 l = t0 l' := by
  unfold t0
  simp only [h]

theorem Aset_congr {l l' : List (Lab q m)} (h : ∀ y, y ∈ l ↔ y ∈ l') : Aset l = Aset l' := by
  unfold Aset
  simp only [h, t0_congr h]

theorem phase_congr {l l' : List (Lab q m)} (h : ∀ y, y ∈ l ↔ y ∈ l') : phase l = phase l' := by
  unfold phase
  rw [Aset_congr h]

theorem t0_map (g : ZMod (q + 1)) (l : List (Lab q m)) : t0 (l.map (sY g)) = t0 l := by
  unfold t0
  congr 1
  ext t
  constructor
  · rintro ⟨y, hy, e⟩
    obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
    exact ⟨y', hy', e⟩
  · rintro ⟨y, hy, e⟩
    exact ⟨sY g y, List.mem_map_of_mem hy, e⟩

theorem Aset_map (g : ZMod (q + 1)) (l : List (Lab q m)) :
    Aset (l.map (sY g)) = (Aset l).image (fun a => a + g) := by
  ext a
  simp only [Aset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, t0_map]
  constructor
  · rintro ⟨y, hy, e1, e2⟩
    obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
    exact ⟨y'.1, ⟨y', hy', rfl, e2⟩, e1⟩
  · rintro ⟨a', ⟨y, hy, e1, e2⟩, rfl⟩
    exact ⟨sY g y, List.mem_map_of_mem hy, by simp [sY, e1], e2⟩

variable [Fact (q + 1).Prime]

theorem Aset_card_ne_zero (l : List (Lab q m)) (hne : l ≠ []) (hl : NF l) :
    ((Aset l).card : ZMod (q + 1)) ≠ 0 := by
  have hS : {t | ∃ y ∈ l, y.2.val = t}.Nonempty := by
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil l hne
    exact ⟨_, y, hy, rfl⟩
  obtain ⟨y, hy, hyt⟩ := Nat.sInf_mem hS
  have hpos : 0 < (Aset l).card :=
    Finset.card_pos.2 ⟨y.1, by
      simp only [Aset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨y, hy, rfl, hyt⟩⟩
  obtain ⟨a, ha⟩ := not_forall.1 (fun h => hl ⟨y.2, h⟩)
  have hlt : (Aset l).card < q + 1 := by
    have hss : Aset l ⊆ (Finset.univ : Finset (ZMod (q + 1))).erase a := by
      intro b hb
      simp only [Aset, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      obtain ⟨y', hy', e1, e2⟩ := hb
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      apply ha
      have : y' = (y'.1, y.2) := Prod.ext rfl (Fin.ext (e2.trans hyt.symm))
      rw [this, e1] at hy'; exact hy'
    have := Finset.card_le_card hss
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card] at this
    omega
  intro h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  exact absurd (Nat.le_of_dvd hpos h0) (by omega)

theorem phase_map (g : ZMod (q + 1)) (l : List (Lab q m)) (hne : l ≠ []) (hl : NF l) :
    phase (l.map (sY g)) = phase l + g := by
  have hn := Aset_card_ne_zero l hne hl
  have hinj : Function.Injective (fun a : ZMod (q + 1) => a + g) := add_left_injective g
  unfold phase
  rw [Aset_map, Finset.sum_image (fun _ _ _ _ e => hinj e), Finset.card_image_of_injective _ hinj,
    Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-! ### projections to a phase -/

noncomputable def proj (g : ZMod (q + 1)) : Ch (Lab q m) →ₗ[ℤ] Ch (Lab q m) :=
  Finsupp.linearCombination ℤ (fun l => if phase l = g then single l 1 else 0)

theorem proj_single_one (g : ZMod (q + 1)) (l : List (Lab q m)) :
    proj g (single l 1) = if phase l = g then single l 1 else 0 := by
  simp [proj, Finsupp.linearCombination_single]

theorem sum_proj (c : Ch (Lab q m)) : ∑ g : ZMod (q + 1), proj g c = c := by
  have : (∑ g : ZMod (q + 1), proj (m := m) g) = LinearMap.id := hom_ext _ _ fun l => by
    simp [LinearMap.sum_apply, proj_single_one]
  simpa [LinearMap.sum_apply] using LinearMap.congr_fun this c

theorem proj_mem_ML (g : ZMod (q + 1)) (r : ℕ) (c : Ch (Lab q m)) (hc : c ∈ ML q m r) :
    proj g c ∈ ML q m r := by
  refine map_supported (proj g) _ _ (fun l hl => ?_) c hc
  rw [proj_single_one]
  split_ifs
  · exact Finsupp.single_mem_supported ℤ _ hl
  · exact Submodule.zero_mem _

theorem proj_mem_D (g : ZMod (q + 1)) (d : Ch (Lab q m)) (hd : d ∈ D (Lab q m)) :
    proj g d ∈ D (Lab q m) := by
  refine D_map (proj g) ?_ d hd
  rintro c (⟨l₁, a, l₂, rfl⟩ | ⟨l₁, a, b, l₂, rfl⟩)
  · rw [proj_single_one]
    split_ifs
    · exact Submodule.subset_span (Or.inl ⟨l₁, a, l₂, rfl⟩)
    · exact Submodule.zero_mem _
  · have e : phase (l₁ ++ b :: a :: l₂) = phase (l₁ ++ a :: b :: l₂) :=
      phase_congr (fun y => by simp only [List.mem_append, List.mem_cons]; tauto)
    rw [map_add, proj_single_one, proj_single_one, e]
    split_ifs
    · exact Submodule.subset_span (Or.inr ⟨l₁, a, b, l₂, rfl⟩)
    · simp

theorem proj_mp (g h : ZMod (q + 1)) (c : Ch (Lab q m)) (hc : c ∈ ML q m 1) :
    proj g (mp (sY h) c) = mp (sY h) (proj (g - h) c) := by
  refine eq_on_supported ((proj g) ∘ₗ (mp (sY h))) ((mp (sY h)) ∘ₗ (proj (g - h))) _
    (fun l hl => ?_) c hc
  have hne : l ≠ [] := by
    rintro rfl
    exact absurd hl.2 (by simp)
  simp only [LinearMap.comp_apply, mp_single, proj_single_one, phase_map h l hne hl.1]
  by_cases e : phase l + h = g
  · have e' : phase l = g - h := by rw [← e]; ring
    simp [e']
  · have e' : ¬ phase l = g - h := fun e' => e (by rw [e']; ring)
    simp [e, e']

/-! ### exactness modulo `D` -/

theorem natCast_val_self (g : ZMod (q + 1)) : ((g.val : ℕ) : ZMod (q + 1)) = g :=
  ZMod.natCast_zmod_val g

/-- `(1 - ω) c ∈ D` implies `c ∈ N·ML + D` -/
theorem exact_one_sub (r : ℕ) (hr : 1 ≤ r) (c : Ch (Lab q m)) (hc : c ∈ ML q m r)
    (h : c - mp (sY 1) c ∈ D (Lab q m)) :
    ∃ b ∈ ML q m r, c - Nop (sY : ZMod (q + 1) → Lab q m → Lab q m) b ∈ D (Lab q m) := by
  have hc1 : c ∈ ML q m 1 := Finsupp.supported_mono (by intro l hl; exact ⟨hl.1, hr.trans hl.2⟩) hc
  refine ⟨proj 0 c, proj_mem_ML 0 r c hc, ?_⟩
  have key : ∀ k : ℕ, proj (k : ZMod (q + 1)) c - mp (sY (k : ZMod (q + 1))) (proj 0 c)
      ∈ D (Lab q m) := by
    intro k
    induction k with
    | zero => simp [sY_zero, mp_id]
    | succ k ih =>
      have h1 := proj_mem_D ((k : ZMod (q + 1)) + 1) _ h
      rw [map_sub, proj_mp _ _ c hc1, add_sub_cancel_right] at h1
      have h2 := mp_mem_D (sY (1 : ZMod (q + 1))) _ ih
      rw [map_sub, mp_mp, sY_comp'] at h2
      have := Submodule.add_mem _ h1 h2
      simpa [Nat.cast_succ] using this
  have e : c - Nop (sY : ZMod (q + 1) → Lab q m → Lab q m) (proj 0 c)
      = ∑ g : ZMod (q + 1), (proj g c - mp (sY g) (proj 0 c)) := by
    rw [Finset.sum_sub_distrib, sum_proj, Nop_apply]
  rw [e]
  refine Submodule.sum_mem _ fun g _ => ?_
  have := key g.val
  rwa [natCast_val_self] at this

theorem tele (r : ℕ) (x : Ch (Lab q m)) (hx : x ∈ ML q m r) (g : ZMod (q + 1)) :
    ∃ b ∈ ML q m r, x - mp (sY g) x = b - mp (sY 1) b := by
  have key : ∀ k : ℕ, ∃ b ∈ ML q m r,
      x - mp (sY (k : ZMod (q + 1))) x = b - mp (sY 1) b := by
    intro k
    induction k with
    | zero => exact ⟨0, Submodule.zero_mem _, by simp [sY_zero, mp_id]⟩
    | succ k ih =>
      obtain ⟨b, hb, e⟩ := ih
      refine ⟨b + mp (sY (k : ZMod (q + 1))) x,
        Submodule.add_mem _ hb (mp_sY_mem_ML _ r x hx), ?_⟩
      rw [map_add, mp_mp, sY_comp', Nat.cast_succ]
      rw [sub_eq_iff_eq_add] at e
      rw [show b + mp (sY (k : ZMod (q + 1))) x - (mp (sY 1) b + mp (sY ((k : ZMod (q + 1)) + 1)) x)
        = (b - mp (sY 1) b) + mp (sY (k : ZMod (q + 1))) x - mp (sY ((k : ZMod (q + 1)) + 1)) x by abel]
      rw [← sub_eq_iff_eq_add] at e
      rw [← e]
      abel
  have := key g.val
  rwa [natCast_val_self] at this

/-- `N c ∈ D` implies `c ∈ (1 - ω)·ML + D` -/
theorem exact_N (r : ℕ) (hr : 1 ≤ r) (c : Ch (Lab q m)) (hc : c ∈ ML q m r)
    (h : Nop (sY : ZMod (q + 1) → Lab q m → Lab q m) c ∈ D (Lab q m)) :
    ∃ b ∈ ML q m r, c - (b - mp (sY 1) b) ∈ D (Lab q m) := by
  have hc1 : c ∈ ML q m 1 := Finsupp.supported_mono (by intro l hl; exact ⟨hl.1, hr.trans hl.2⟩) hc
  choose b hb hbe using fun g : ZMod (q + 1) =>
    tele r (proj g c) (proj_mem_ML g r c hc) (-g)
  refine ⟨∑ g, b g, Submodule.sum_mem _ fun g _ => hb g, ?_⟩
  have h0 := proj_mem_D 0 _ h
  have e1 : ∑ g, b g - mp (sY 1) (∑ g, b g)
      = ∑ g : ZMod (q + 1), (proj g c - mp (sY (-g)) (proj g c)) := by
    rw [map_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun g _ => (hbe g).symm
  have e2 : proj 0 (Nop (sY : ZMod (q + 1) → Lab q m → Lab q m) c)
      = ∑ g : ZMod (q + 1), mp (sY (-g)) (proj g c) := by
    rw [Nop_apply, map_sum,
      ← Equiv.sum_comp (Equiv.neg (ZMod (q + 1))) (fun g => proj 0 (mp (sY g) c))]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Equiv.neg_apply, proj_mp _ _ c hc1, zero_sub, neg_neg]
  have e : c - (∑ g, b g - mp (sY 1) (∑ g, b g))
      = proj 0 (Nop (sY : ZMod (q + 1) → Lab q m → Lab q m) c) := by
    rw [e1, e2, Finset.sum_sub_distrib, sum_proj]
    abel
  rw [e]
  exact h0

end target

end Ziegler2002.Dev
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Ziegler2002.Dev

open Finsupp

section prismsupp

variable {α : Type*} [Preorder α]

theorem PL_mem_supported (g : α → α) (hg : Monotone g) (hle : ∀ x, x ≤ g x) :
    ∀ l : List α, l.Pairwise (· ≤ ·) →
      PL g l ∈ Finsupp.supported ℤ ℤ {l' : List α | l'.Pairwise (· ≤ ·) ∧
        (∀ y ∈ l', y ∈ l ∨ ∃ z ∈ l, y = g z) ∧ l'.length = l.length + 1} := by
  intro l
  induction l with
  | nil => intro _; simp [PL]
  | cons x l ih =>
    intro hp
    obtain ⟨hx, hl⟩ := List.pairwise_cons.1 hp
    have e : PL g (x :: l) = cons x (single ((x :: l).map g) 1) - cons x (PL g l) := by
      simp [PL]
    rw [e]
    refine Submodule.sub_mem _ ?_ ?_
    · rw [cons_single]
      refine Finsupp.single_mem_supported ℤ _ ⟨?_, ?_, ?_⟩
      · refine List.pairwise_cons.2 ⟨?_, List.Pairwise.map g (fun a b h => hg h) hp⟩
        intro y hy
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hle _
        · exact (hx z hz).trans (hle z)
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Or.inl List.mem_cons_self
        · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
          exact Or.inr ⟨z, hz, rfl⟩
      · simp
    · refine map_supported (cons x) _ _ (fun l' hl' => ?_) _ (ih hl)
      obtain ⟨h1, h2, h3⟩ := hl'
      rw [cons_single]
      refine Finsupp.single_mem_supported ℤ _ ⟨?_, ?_, ?_⟩
      · refine List.pairwise_cons.2 ⟨?_, h1⟩
        intro y hy
        rcases h2 y hy with hy | ⟨z, hz, rfl⟩
        · exact hx y hy
        · exact (hx z hz).trans (hle z)
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Or.inl List.mem_cons_self
        · rcases h2 y hy with hy | ⟨z, hz, rfl⟩
          · exact Or.inl (List.mem_cons_of_mem _ hy)
          · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, rfl⟩
      · simp [h3]

end prismsupp

section source

variable {q n : ℕ}

abbrev Tp (q n : ℕ) := ZMod (q + 1) → Finset (Fin n)

def Valid (X : Tp q n) : Prop :=
  (∀ i j, i ≠ j → Disjoint (X i) (X j)) ∧ ∃ i, (X i).Nonempty

def sT (g : ZMod (q + 1)) (X : Tp q n) : Tp q n := fun i => X (i - g)

def Below (k : ℕ) (X : Tp q n) : Prop := ∀ i, ∀ a ∈ X i, a.val < k

def eT (c : Fin n) : Tp q n := fun i => if i = 0 then {c} else ∅

def gT (c : Fin n) (X : Tp q n) : Tp q n := X ⊔ eT c

theorem sT_comp (g u : ZMod (q + 1)) : (sT g : Tp q n → Tp q n) ∘ sT u = sT (g + u) := by
  funext X i
  simp only [sT, Function.comp_apply]
  congr 1
  ring

theorem sT_comp' (g u : ZMod (q + 1)) : (sT u : Tp q n → Tp q n) ∘ sT g = sT (g + u) := by
  funext X i
  simp only [sT, Function.comp_apply]
  congr 1
  ring

theorem sT_zero : (sT 0 : Tp q n → Tp q n) = id := by
  funext X i
  simp [sT]

theorem Valid_sT (g : ZMod (q + 1)) {X : Tp q n} (h : Valid X) : Valid (sT g X) := by
  refine ⟨fun i j hij => h.1 _ _ (fun e => hij (sub_left_injective e)), ?_⟩
  obtain ⟨i, hi⟩ := h.2
  exact ⟨i + g, by simpa [sT] using hi⟩

theorem Below_sT (g : ZMod (q + 1)) {k : ℕ} {X : Tp q n} (h : Below k X) : Below k (sT g X) :=
  fun i a ha => h (i - g) a ha

theorem sT_mono (g : ZMod (q + 1)) {X Y : Tp q n} (h : X ≤ Y) : sT g X ≤ sT g Y :=
  fun i => h (i - g)

theorem Below_mono {k k' : ℕ} (hk : k ≤ k') {X : Tp q n} (h : Below k X) : Below k' X :=
  fun i a ha => (h i a ha).trans_le hk

theorem Valid_eT (c : Fin n) : Valid (eT c : Tp q n) := by
  refine ⟨fun i j hij => ?_, ⟨0, c, by simp [eT]⟩⟩
  by_cases hi : i = 0
  · have hj : j ≠ 0 := fun hj => hij (hi.trans hj.symm)
    simp [eT, hj]
  · simp [eT, hi]

theorem Below_eT (c : Fin n) {k : ℕ} (hc : c.val < k) : Below k (eT c : Tp q n) := by
  intro i a ha
  by_cases hi : i = 0
  · simp only [eT, hi, if_true, Finset.mem_singleton] at ha
    rw [ha]; exact hc
  · simp [eT, hi] at ha

theorem le_gT (c : Fin n) (X : Tp q n) : X ≤ gT c X := le_sup_left

theorem eT_le_gT (c : Fin n) (X : Tp q n) : eT c ≤ gT c X := le_sup_right

theorem gT_mono (c : Fin n) : Monotone (gT c : Tp q n → Tp q n) :=
  fun _ _ h => sup_le_sup_right h _

theorem gT_apply (c : Fin n) (X : Tp q n) (i : ZMod (q + 1)) :
    gT c X i = X i ∪ (if i = 0 then {c} else ∅) := rfl

theorem Valid_gT (c : Fin n) {X : Tp q n} (h : Valid X) (hc : ∀ i, c ∉ X i) :
    Valid (gT c X) := by
  refine ⟨fun i j hij => ?_, ?_⟩
  · rw [gT_apply, gT_apply, Finset.disjoint_union_left, Finset.disjoint_union_right,
      Finset.disjoint_union_right]
    refine ⟨⟨h.1 i j hij, ?_⟩, ?_, ?_⟩
    · split_ifs
      · exact Finset.disjoint_singleton_right.2 (hc i)
      · exact Finset.disjoint_empty_right _
    · split_ifs
      · exact Finset.disjoint_singleton_left.2 (hc j)
      · exact Finset.disjoint_empty_left _
    · by_cases hi : i = 0
      · have hj : j ≠ 0 := fun hj => hij (hi.trans hj.symm)
        simp [hj]
      · simp [hi]
  · obtain ⟨i, hi⟩ := h.2
    exact ⟨i, hi.mono (by rw [gT_apply]; exact Finset.subset_union_left)⟩

theorem Below_gT (c : Fin n) {k k' : ℕ} {X : Tp q n} (h : Below k X) (hk : k ≤ k')
    (hc : c.val < k') : Below k' (gT c X) := by
  intro i a ha
  rw [gT_apply, Finset.mem_union] at ha
  rcases ha with ha | ha
  · exact (h i a ha).trans_le hk
  · split_ifs at ha
    · rw [Finset.mem_singleton.1 ha]; exact hc
    · simp at ha

/-- sorted lists of `k+1` valid points supported in the first `k+1` coordinates -/
def Good (k : ℕ) (l : List (Tp q n)) : Prop :=
  l.Pairwise (· ≤ ·) ∧ (∀ X ∈ l, Valid X ∧ Below (k + 1) X) ∧ l.length = k + 1

theorem Good_map_sT (g : ZMod (q + 1)) {k : ℕ} {l : List (Tp q n)} (h : Good k l) :
    Good k (l.map (sT g)) := by
  refine ⟨List.Pairwise.map _ (fun a b hab => sT_mono g hab) h.1, ?_, by simpa using h.2.2⟩
  intro X hX
  obtain ⟨X', hX', rfl⟩ := List.mem_map.1 hX
  exact ⟨Valid_sT g (h.2.1 X' hX').1, Below_sT g (h.2.1 X' hX').2⟩

theorem fill_good (c : Fin n) (k : ℕ) (hc : c.val = k + 1) (z : Ch (Tp q n))
    (hz : z ∈ Finsupp.supported ℤ ℤ {l : List (Tp q n) | Good k l}) :
    fill (eT c) (gT c) z ∈ Finsupp.supported ℤ ℤ {l : List (Tp q n) | Good (k + 1) l} := by
  have hfill : fill (eT c) (gT c) z
      = ((cons (eT c)) ∘ₗ (mp (gT c)) - P (gT c) : Ch (Tp q n) →ₗ[ℤ] Ch (Tp q n)) z := rfl
  rw [hfill]
  refine map_supported _ _ _ (fun l hl => ?_) z hz
  obtain ⟨h1, h2, h3⟩ := hl
  have hg : ∀ X ∈ l, Valid (gT c X) ∧ Below (k + 1 + 1) (gT c X) := fun X hX =>
    ⟨Valid_gT c (h2 X hX).1 (fun i hi => by have := (h2 X hX).2 i c hi; omega),
      Below_gT c (h2 X hX).2 (by omega) (by omega)⟩
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, mp_single, cons_single, P_single_one]
  refine Submodule.sub_mem _ (Finsupp.single_mem_supported ℤ _ ⟨?_, ?_, ?_⟩) ?_
  · refine List.pairwise_cons.2 ⟨?_, List.Pairwise.map _ (fun a b hab => gT_mono c hab) h1⟩
    intro y hy
    obtain ⟨z, _, rfl⟩ := List.mem_map.1 hy
    exact eT_le_gT c z
  · intro X hX
    rcases List.mem_cons.1 hX with rfl | hX
    · exact ⟨Valid_eT c, Below_eT c (by omega)⟩
    · obtain ⟨X', hX', rfl⟩ := List.mem_map.1 hX
      exact hg X' hX'
  · simp [h3]
  · refine Finsupp.supported_mono ?_ (PL_mem_supported (gT c) (gT_mono c) (le_gT c) l h1)
    rintro l' ⟨p1, p2, p3⟩
    refine ⟨p1, ?_, by rw [p3, h3]⟩
    intro X hX
    rcases p2 X hX with hX | ⟨X', hX', rfl⟩
    · exact ⟨(h2 X hX).1, Below_mono (by omega) (h2 X hX).2⟩
    · exact hg X' hX'

/-- the `k`-th coordinate -/
def cK (hn : 0 < n) (k : ℕ) : Fin n := if h : k < n then ⟨k, h⟩ else ⟨0, hn⟩

theorem cK_val (hn : 0 < n) (k : ℕ) (hk : k < n) : (cK hn k).val = k := by
  simp [cK, hk]

/-- the chains `h_k` with `∂ h_{k+1} = τ_{k+1} h_k` -/
noncomputable def hseq (q : ℕ) (hn : 0 < n) : ℕ → Ch (Tp q n)
  | 0 => single [eT (cK hn 0)] 1
  | k + 1 => fill (eT (cK hn (k + 1))) (gT (cK hn (k + 1)))
      (tau (1 : ZMod (q + 1)) sT (k + 1) (hseq q hn k))

theorem bd_hseq_zero (hn : 0 < n) : bd (hseq q hn 0) = single [] 1 := by
  simp [hseq, bdL]

theorem bd_hseq_succ (hn : 0 < n) (k : ℕ) :
    bd (hseq q hn (k + 1)) = tau (1 : ZMod (q + 1)) sT (k + 1) (hseq q hn k) := by
  rw [hseq]
  apply bd_fill
  rw [bd_tau]
  cases k with
  | zero =>
    rw [bd_hseq_zero, tau_odd _ _ _ (by norm_num)]
    simp
  | succ k =>
    rw [bd_hseq_succ hn k]
    exact tau_tau 1 sT (fun g => sT_comp g 1) (fun g => sT_comp' g 1) (k + 1) _

theorem hseq_good (hn : 0 < n) (k : ℕ) (hk : k < n) :
    hseq q hn k ∈ Finsupp.supported ℤ ℤ {l : List (Tp q n) | Good k l} := by
  induction k with
  | zero =>
    refine Finsupp.single_mem_supported ℤ _ ⟨by simp, ?_, rfl⟩
    intro X hX
    rw [List.mem_singleton] at hX
    subst hX
    exact ⟨Valid_eT _, Below_eT _ (by rw [cK_val hn 0 hk]; omega)⟩
  | succ k ih =>
    rw [hseq]
    refine fill_good _ k (cK_val hn (k + 1) hk) _ ?_
    exact tau_mem_supported 1 sT {l : List (Tp q n) | Good k l}
      (fun l hl g => Good_map_sT g hl) (k + 1) _ (ih (by omega))

end source

end Ziegler2002.Dev
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Ziegler2002.Dev

open Finsupp

section main

variable {q m n : ℕ} [Fact (q + 1).Prime]

theorem tau_add_two {G α : Type*} [Fintype G] (u : G) (σ : G → α → α) (j : ℕ) :
    tau u σ (j + 2) = tau u σ j := by
  simp [tau]

/-- the descent: a sequence of label chains with `∂ g_{k+1} = τ_{k+1} g_k` that dies modulo
`D` in degree `K` has `g_0 ∈ ∂ + N + D`. -/
theorem descent (K : ℕ) (gk : ℕ → Ch (Lab q m)) (h1 : ∀ k ≤ K, gk k ∈ ML q m (k + 1))
    (h2 : ∀ k < K, bd (gk (k + 1)) = tau (1 : ZMod (q + 1)) sY (k + 1) (gk k))
    (h3 : gk K ∈ D (Lab q m)) :
    ∃ a b : Ch (Lab q m),
      gk 0 - (bd a + Nop (sY : ZMod (q + 1) → Lab q m → Lab q m) b) ∈ D (Lab q m) := by
  have key : ∀ j ≤ K, ∃ a b : Ch (Lab q m), b ∈ ML q m (K - j + 1) ∧
      gk (K - j) - (bd a + tau (1 : ZMod (q + 1)) sY (K - j + 2) b) ∈ D (Lab q m) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨0, 0, Submodule.zero_mem _, by simpa using h3⟩
    | succ j ih =>
      intro hj
      obtain ⟨a', b', hb', hd⟩ := ih (by omega)
      obtain ⟨k, hk⟩ : ∃ k, K - (j + 1) = k := ⟨_, rfl⟩
      have hk1 : K - j = k + 1 := by omega
      rw [hk]
      rw [hk1] at hb' hd
      have hd' := bd_mem_D _ hd
      rw [map_sub, map_add, bd_bd, zero_add, h2 k (by omega), bd_tau, tau_add_two,
        ← map_sub] at hd'
      have hc : gk k - bd b' ∈ ML q m (k + 1) :=
        Submodule.sub_mem _ (h1 k (by omega)) (bd_mem_ML (k + 1) b' hb')
      rcases Nat.mod_two_eq_zero_or_one (k + 1) with hpar | hpar
      · rw [tau_even _ _ _ hpar] at hd'
        obtain ⟨b, hb, hbd⟩ := exact_N (k + 1) (by omega) _ hc hd'
        refine ⟨b', b, hb, ?_⟩
        rw [tau_odd _ _ _ (by omega), ← sub_sub]
        exact hbd
      · rw [tau_odd _ _ _ hpar] at hd'
        obtain ⟨b, hb, hbd⟩ := exact_one_sub (k + 1) (by omega) _ hc hd'
        refine ⟨b', b, hb, ?_⟩
        rw [tau_even _ _ _ (by omega), ← sub_sub]
        exact hbd
  obtain ⟨a, b, _, hd⟩ := key K le_rfl
  refine ⟨a, b, ?_⟩
  simpa [tau_even (1 : ZMod (q + 1)) (sY : ZMod (q + 1) → Lab q m → Lab q m) 2 (by norm_num)]
    using hd

theorem lam_sT (lam : Tp q n → Lab q m)
    (hlam : ∀ X, Valid X → lam (sT 1 X) = sY 1 (lam X)) (g : ZMod (q + 1)) (X : Tp q n)
    (hX : Valid X) : lam (sT g X) = sY g (lam X) := by
  have key : ∀ k : ℕ, lam (sT (k : ZMod (q + 1)) X) = sY (k : ZMod (q + 1)) (lam X) := by
    intro k
    induction k with
    | zero => simp [sT_zero, sY_zero]
    | succ k ih =>
      have e1 : sT ((k : ZMod (q + 1)) + 1) X = sT 1 (sT (k : ZMod (q + 1)) X) :=
        (congrFun (sT_comp' (k : ZMod (q + 1)) 1) X).symm
      have e2 : sY ((k : ZMod (q + 1)) + 1) (lam X) = sY 1 (sY (k : ZMod (q + 1)) (lam X)) :=
        (congrFun (sY_comp' (k : ZMod (q + 1)) 1) (lam X)).symm
      rw [Nat.cast_succ, e1, e2, hlam _ (Valid_sT _ hX), ih]
  have := key g.val
  rwa [natCast_val_self] at this

theorem main (hn : 1 ≤ n) (hmn : m ≤ (n - 1) / q) (lam : Tp q n → Lab q m)
    (hlam : ∀ X, Valid X → lam (sT 1 X) = sY 1 (lam X)) :
    ∃ l : List (Tp q n), l.Pairwise (· ≤ ·) ∧ (∀ X ∈ l, Valid X) ∧ ¬ NF (l.map lam) := by
  by_contra hno
  have hno' : ∀ l : List (Tp q n), l.Pairwise (· ≤ ·) → (∀ X ∈ l, Valid X) → NF (l.map lam) := by
    intro l hp hv
    by_contra h
    exact hno ⟨l, hp, hv, h⟩
  have hq : 0 < q := by
    have := (Fact.out : (q + 1).Prime).two_le
    omega
  have hn0 : 0 < n := hn
  have hK : m * q < n := by
    have := (Nat.le_div_iff_mul_le hq).1 hmn
    omega
  set gk : ℕ → Ch (Lab q m) := fun k => mp lam (hseq q hn0 k) with hgk
  have h1 : ∀ k ≤ m * q, gk k ∈ ML q m (k + 1) := by
    intro k hk
    refine map_supported (mp lam) _ _ (fun l hl => ?_) _ (hseq_good hn0 k (by omega))
    rw [mp_single]
    exact Finsupp.single_mem_supported ℤ _
      ⟨hno' l hl.1 (fun X hX => (hl.2.1 X hX).1), by simp [hl.2.2]⟩
  have h2 : ∀ k < m * q, bd (gk (k + 1)) = tau (1 : ZMod (q + 1)) sY (k + 1) (gk k) := by
    intro k hk
    simp only [hgk]
    rw [bd_mp, bd_hseq_succ]
    exact mp_tau 1 sT sY lam {l : List (Tp q n) | Good k l}
      (fun l hl X hX g => lam_sT lam hlam g X (hl.2.1 X hX).1) (k + 1) _
      (hseq_good hn0 k (by omega))
  have h3 : gk (m * q) ∈ D (Lab q m) := by
    refine map_supported (mp lam) _ _ (fun l hl => ?_) _ (hseq_good hn0 (m * q) hK)
    rw [mp_single]
    refine single_mem_D_of_not_nodup _ (fun hnd => ?_)
    have := card_le_of_NF _ (hno' l hl.1 (fun X hX => (hl.2.1 X hX).1)) hnd
    rw [List.length_map, hl.2.2, Nat.mul_comm] at this
    omega
  obtain ⟨a, b, hd⟩ := descent (m * q) gk h1 h2 h3
  have h0 := apply_nil_of_mem_D _ (bd_mem_D _ hd)
  have e0 : bd (gk 0) = single [] 1 := by
    simp only [hgk]
    rw [bd_mp, bd_hseq_zero]
    simp
  rw [map_sub, map_add, bd_bd, zero_add, e0, Nop_apply, map_sum] at h0
  simp only [bd_mp, Finsupp.sub_apply, Finsupp.finsetSum_apply, mp_apply_nil,
    Finsupp.single_eq_same, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul] at h0
  have hdvd : ((q : ℤ) + 1) ∣ 1 := ⟨(bd b) [], by push_cast at h0; linarith⟩
  have := Int.eq_one_of_dvd_one (by positivity) hdvd
  omega

end main

/-- Ziegler's `Z_p`-Tucker lemma, in the published form. -/
theorem zp_tucker_dev (q : ℕ) (hp : (q + 1).Prime) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hmn : m ≤ (n - 1) / q)
    (lam : (Fin (q + 1) → Finset (Fin n)) → Fin (q + 1) × Fin m)
    (hlam : ∀ X : Fin (q + 1) → Finset (Fin n),
      (∀ i j, i ≠ j → Disjoint (X i) (X j)) → (∃ i, (X i).Nonempty) →
        lam (fun i => X (i - 1)) = ((lam X).1 + 1, (lam X).2)) :
    ∃ Y : Fin (q + 1) → Fin (q + 1) → Finset (Fin n),
      (∀ j, (∀ i i', i ≠ i' → Disjoint (Y j i) (Y j i')) ∧ ∃ i, (Y j i).Nonempty) ∧
      StrictMono Y ∧ (∀ j j', (lam (Y j)).2 = (lam (Y j')).2) ∧
      Function.Injective (fun j => (lam (Y j)).1) := by
  have : Fact (q + 1).Prime := ⟨hp⟩
  obtain ⟨l, hpw, hv, hnf⟩ := main (q := q) (m := m) (n := n) hn hmn lam
    (fun X hX => hlam X hX.1 hX.2)
  obtain ⟨t, ht⟩ := not_not.1 hnf
  have hex : ∀ a : Fin (q + 1), ∃ i : Fin l.length, lam (l.get i) = (a, t) := by
    intro a
    obtain ⟨X, hX, e⟩ := List.mem_map.1 (ht a)
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hX
    exact ⟨i, e⟩
  choose idx hidx using hex
  have hinj : Function.Injective idx := by
    intro a a' e
    have h1 := hidx a
    rw [e] at h1
    exact (Prod.mk.inj (h1.symm.trans (hidx a'))).1
  have hF : (Finset.univ.image idx).card = q + 1 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  set emb := (Finset.univ.image idx).orderEmbOfFin hF with hemb
  have hmem : ∀ j, ∃ a, idx a = emb j := fun j => by
    obtain ⟨a, _, ha⟩ := Finset.mem_image.1
      (Finset.orderEmbOfFin_mem (Finset.univ.image idx) hF j)
    exact ⟨a, ha⟩
  choose a ha using hmem
  have hlamY : ∀ j, lam (l.get (emb j)) = (a j, t) := fun j => by rw [← ha j]; exact hidx _
  have hainj : Function.Injective a := by
    intro j j' e
    have : emb j = emb j' := by rw [← ha j, ← ha j', e]
    exact emb.injective this
  refine ⟨fun j => l.get (emb j), fun j => hv _ (List.get_mem _ _), ?_, ?_, ?_⟩
  · intro j j' hjj
    have hlt : emb j < emb j' := emb.strictMono hjj
    have hle : l.get (emb j) ≤ l.get (emb j') := List.pairwise_iff_get.1 hpw _ _ hlt
    refine lt_of_le_of_ne hle (fun e => ?_)
    have : (a j, t) = (a j', t) := (hlamY j).symm.trans ((congrArg lam e).trans (hlamY j'))
    exact hjj.ne (hainj (Prod.mk.inj this).1)
  · intro j j'
    simp only [hlamY]
  · intro j j' e
    simp only [hlamY] at e
    exact hainj e

end Ziegler2002.Dev
end

theorem solution : type_of% @Ziegler2002.Dev.zp_tucker_dev := @Ziegler2002.Dev.zp_tucker_dev
