-- Prove2me | solution 1 for SymBoolPCSP.Galois.transitivity
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:10:27.644755+00:00
-- url     : https://prove2.me/submissions/d4a41671-031b-4cca-89c7-ac343f238185

import Mathlib
import Definitions.Def_SymBoolPCSP_Galois_Basic

open PCSPBLPAff.Symmetric
open SymBoolPCSP.Galois

set_option linter.unusedVariables false

lemma pppDefinable_univ {τ : Type} {ar : τ → ℕ} {D : Type} (𝒜 ℬ : RelStruct τ ar D) (k : ℕ) :
    PPPDefinable 𝒜 ℬ (Set.univ : Set (Fin k → D)) Set.univ := by
  refine ⟨0, ⟨k + 0, 0, Fin.elim0, fun j => Fin.elim0 j⟩, rfl, ?_, ?_⟩
  · intro x _
    exact ⟨Fin.elim0, fun j => Fin.elim0 j⟩
  · intro _ _
    exact Set.mem_univ _

lemma pppDefinable_withEqual_self {τ : Type} {ar : τ → ℕ} {D : Type} (𝒜 ℬ : RelStruct τ ar D)
    (s : τ ⊕ Unit) :
    PPPDefinable 𝒜 ℬ ((withEqual 𝒜).rel s) ((withEqual ℬ).rel s) := by
  refine ⟨0, ⟨arEq ar s + 0, 1, fun _ => s, fun _ i => Fin.castAdd 0 i⟩, rfl, ?_, ?_⟩
  · intro x hx
    refine ⟨Fin.elim0, fun _ => ?_⟩
    convert hx using 1
    ext i
    simp [Function.comp]
  · intro z hz
    exact hz 0

lemma pppDefinable_pullback {τ : Type} {ar : τ → ℕ} {D : Type} (𝒜 ℬ : RelStruct τ ar D)
    {r k : ℕ} {P Q : Set (Fin r → D)} (hPQ : PPPDefinable 𝒜 ℬ P Q) (sc : Fin r → Fin k) :
    PPPDefinable 𝒜 ℬ {x : Fin k → D | x ∘ sc ∈ P} {x : Fin k → D | x ∘ sc ∈ Q} := by
  rcases hPQ with ⟨ℓ, Ψ, h, hP, hQ⟩
  let varMap : Fin Ψ.n → Fin (k + ℓ) :=
    fun v => Fin.append (fun i => Fin.castAdd ℓ (sc i)) (Fin.natAdd k) (Fin.cast h v)
  refine ⟨ℓ, ⟨k + ℓ, Ψ.m, Ψ.sym, fun j i => varMap (Ψ.scope j i)⟩, rfl, ?_, ?_⟩
  · intro x hx
    rcases hP (x ∘ sc) hx with ⟨y, hy⟩
    refine ⟨y, fun j => ?_⟩
    convert hy j using 1
    ext i
    dsimp [Function.comp, varMap]
    generalize Fin.cast h (Ψ.scope j i) = u
    refine Fin.addCases (fun i => ?_) (fun i => ?_) u <;> simp [Function.comp]
  · intro z hz
    have hmem := hQ (z ∘ varMap) (fun j => hz j)
    change (fun i : Fin k => z (Fin.castAdd ℓ i)) ∘ sc ∈ Q
    convert hmem using 1
    ext i
    simp [varMap, Function.comp]

lemma pppDefinable_inter {τ : Type} {ar : τ → ℕ} {D : Type} (𝒜 ℬ : RelStruct τ ar D)
    {k : ℕ} {P₁ Q₁ P₂ Q₂ : Set (Fin k → D)}
    (h₁ : PPPDefinable 𝒜 ℬ P₁ Q₁) (h₂ : PPPDefinable 𝒜 ℬ P₂ Q₂) :
    PPPDefinable 𝒜 ℬ (P₁ ∩ P₂) (Q₁ ∩ Q₂) := by
  rcases h₁ with ⟨ℓ₁, Ψ₁, h₁_n, hP₁, hQ₁⟩
  rcases h₂ with ⟨ℓ₂, Ψ₂, h₂_n, hP₂, hQ₂⟩
  let varMap₁ : Fin Ψ₁.n → Fin (k + (ℓ₁ + ℓ₂)) :=
    fun v => Fin.append (Fin.castAdd (ℓ₁ + ℓ₂)) (fun i => Fin.natAdd k (Fin.castAdd ℓ₂ i))
      (Fin.cast h₁_n v)
  let varMap₂ : Fin Ψ₂.n → Fin (k + (ℓ₁ + ℓ₂)) :=
    fun v => Fin.append (Fin.castAdd (ℓ₁ + ℓ₂)) (fun i => Fin.natAdd k (Fin.natAdd ℓ₁ i))
      (Fin.cast h₂_n v)
  let clause : Fin (Ψ₁.m + Ψ₂.m) → Σ s : τ ⊕ Unit, (Fin (arEq ar s) → Fin (k + (ℓ₁ + ℓ₂))) :=
    Fin.append
      (fun j₁ => ⟨Ψ₁.sym j₁, varMap₁ ∘ Ψ₁.scope j₁⟩)
      (fun j₂ => ⟨Ψ₂.sym j₂, varMap₂ ∘ Ψ₂.scope j₂⟩)
  refine ⟨ℓ₁ + ℓ₂, ⟨k + (ℓ₁ + ℓ₂), Ψ₁.m + Ψ₂.m, fun j => (clause j).1, fun j => (clause j).2⟩,
    rfl, ?_, ?_⟩
  · rintro x ⟨hx₁, hx₂⟩
    rcases hP₁ x hx₁ with ⟨y₁, hy₁⟩
    rcases hP₂ x hx₂ with ⟨y₂, hy₂⟩
    refine ⟨Fin.append y₁ y₂, ?_⟩
    have h_eq₁ : ∀ v : Fin Ψ₁.n,
        Fin.append x (Fin.append y₁ y₂) (varMap₁ v) = Fin.append x y₁ (Fin.cast h₁_n v) := by
      intro v
      dsimp [varMap₁]
      generalize Fin.cast h₁_n v = u
      refine Fin.addCases (fun i => ?_) (fun i => ?_) u <;> simp
    have h_eq₂ : ∀ v : Fin Ψ₂.n,
        Fin.append x (Fin.append y₁ y₂) (varMap₂ v) = Fin.append x y₂ (Fin.cast h₂_n v) := by
      intro v
      dsimp [varMap₂]
      generalize Fin.cast h₂_n v = u
      refine Fin.addCases (fun i => ?_) (fun i => ?_) u <;> simp
    intro j
    change (let c := clause j;
      (fun v => Fin.append x (Fin.append y₁ y₂) v) ∘ c.2 ∈ (withEqual 𝒜).rel c.1)
    refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
    · dsimp [clause]
      rw [Fin.append_left]
      dsimp
      have hcomp : (fun v => Fin.append x (Fin.append y₁ y₂) v) ∘ (varMap₁ ∘ Ψ₁.scope j₁) =
          (fun v => Fin.append x y₁ (Fin.cast h₁_n v)) ∘ Ψ₁.scope j₁ := by
        ext i
        exact h_eq₁ (Ψ₁.scope j₁ i)
      rw [hcomp]
      exact hy₁ j₁
    · dsimp [clause]
      rw [Fin.append_right]
      dsimp
      have hcomp : (fun v => Fin.append x (Fin.append y₁ y₂) v) ∘ (varMap₂ ∘ Ψ₂.scope j₂) =
          (fun v => Fin.append x y₂ (Fin.cast h₂_n v)) ∘ Ψ₂.scope j₂ := by
        ext i
        exact h_eq₂ (Ψ₂.scope j₂ i)
      rw [hcomp]
      exact hy₂ j₂
  · intro z hz
    have hz₁ : Satisfies Ψ₁ (withEqual ℬ) (z ∘ varMap₁) := by
      intro j₁
      have h := hz (Fin.castAdd Ψ₂.m j₁)
      change (let c := clause (Fin.castAdd Ψ₂.m j₁); z ∘ c.2 ∈ (withEqual ℬ).rel c.1) at h
      dsimp [clause] at h
      rw [Fin.append_left] at h
      exact h
    have hz₂ : Satisfies Ψ₂ (withEqual ℬ) (z ∘ varMap₂) := by
      intro j₂
      have h := hz (Fin.natAdd Ψ₁.m j₂)
      change (let c := clause (Fin.natAdd Ψ₁.m j₂); z ∘ c.2 ∈ (withEqual ℬ).rel c.1) at h
      dsimp [clause] at h
      rw [Fin.append_right] at h
      exact h
    have hmem₁ := hQ₁ (z ∘ varMap₁) hz₁
    have hmem₂ := hQ₂ (z ∘ varMap₂) hz₂
    have heq₁ : (fun i : Fin k => (z ∘ varMap₁) (Fin.cast h₁_n.symm (Fin.castAdd ℓ₁ i))) =
        (fun i : Fin k => z (Fin.castAdd (ℓ₁ + ℓ₂) i)) := by
      ext i
      simp [varMap₁, Function.comp]
    have heq₂ : (fun i : Fin k => (z ∘ varMap₂) (Fin.cast h₂_n.symm (Fin.castAdd ℓ₂ i))) =
        (fun i : Fin k => z (Fin.castAdd (ℓ₁ + ℓ₂) i)) := by
      ext i
      simp [varMap₂, Function.comp]
    rw [heq₁] at hmem₁
    rw [heq₂] at hmem₂
    exact ⟨hmem₁, hmem₂⟩

lemma pppDefinable_biInter {τ : Type} {ar : τ → ℕ} {D : Type} (𝒜 ℬ : RelStruct τ ar D)
    {k : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι) (P Q : ι → Set (Fin k → D))
    (h : ∀ i ∈ s, PPPDefinable 𝒜 ℬ (P i) (Q i)) :
    PPPDefinable 𝒜 ℬ {x | ∀ i ∈ s, x ∈ P i} {x | ∀ i ∈ s, x ∈ Q i} := by
  induction s using Finset.induction_on with
  | empty =>
    have huniv := pppDefinable_univ 𝒜 ℬ k
    have hP : {x : Fin k → D | ∀ i ∈ (∅ : Finset ι), x ∈ P i} = Set.univ := by
      ext x; simp
    have hQ : {x : Fin k → D | ∀ i ∈ (∅ : Finset ι), x ∈ Q i} = Set.univ := by
      ext x; simp
    rw [hP, hQ]
    exact huniv
  | @insert a s ha ih =>
    have ha_def := h a (Finset.mem_insert_self a s)
    have hs_def := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hinter := pppDefinable_inter 𝒜 ℬ ha_def hs_def
    have hP : {x : Fin k → D | ∀ i ∈ insert a s, x ∈ P i} =
        P a ∩ {x : Fin k → D | ∀ i ∈ s, x ∈ P i} := by
      ext x; simp [Set.mem_inter_iff]
    have hQ : {x : Fin k → D | ∀ i ∈ insert a s, x ∈ Q i} =
        Q a ∩ {x : Fin k → D | ∀ i ∈ s, x ∈ Q i} := by
      ext x; simp [Set.mem_inter_iff]
    rw [hP, hQ]
    exact hinter

lemma pppDefinable_proj {τ : Type} {ar : τ → ℕ} {D : Type} (𝒜 ℬ : RelStruct τ ar D)
    {k ℓ₀ : ℕ} {P_ext Q_ext : Set (Fin (k + ℓ₀) → D)}
    (h_ext : PPPDefinable 𝒜 ℬ P_ext Q_ext)
    {P Q : Set (Fin k → D)}
    (hP : ∀ x ∈ P, ∃ y₀ : Fin ℓ₀ → D, Fin.append x y₀ ∈ P_ext)
    (hQ : ∀ z₀ : Fin (k + ℓ₀) → D, z₀ ∈ Q_ext → (fun i : Fin k => z₀ (Fin.castAdd ℓ₀ i)) ∈ Q) :
    PPPDefinable 𝒜 ℬ P Q := by
  rcases h_ext with ⟨ℓ, Ψ, h, hP_ext, hQ_ext⟩
  have h' : Ψ.n = k + (ℓ₀ + ℓ) := h.trans (Nat.add_assoc k ℓ₀ ℓ)
  refine ⟨ℓ₀ + ℓ, Ψ, h', ?_, ?_⟩
  · intro x hx
    rcases hP x hx with ⟨y₀, hy₀⟩
    rcases hP_ext (Fin.append x y₀) hy₀ with ⟨y, hy⟩
    refine ⟨Fin.append y₀ y, ?_⟩
    have h_eq : (fun v => Fin.append x (Fin.append y₀ y) (Fin.cast h' v)) =
        (fun v => Fin.append (Fin.append x y₀) y (Fin.cast h v)) := by
      ext v
      have hcast : Fin.cast h' v = Fin.cast (Nat.add_assoc k ℓ₀ ℓ) (Fin.cast h v) := rfl
      rw [hcast]
      generalize Fin.cast h v = u
      refine Fin.addCases (fun u₁ => ?_) (fun u₂ => ?_) u
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) u₁
        · have hc : Fin.cast (Nat.add_assoc k ℓ₀ ℓ) (Fin.castAdd ℓ (Fin.castAdd ℓ₀ i)) =
              Fin.castAdd (ℓ₀ + ℓ) i := by
            ext; rfl
          rw [hc]
          simp
        · have hc : Fin.cast (Nat.add_assoc k ℓ₀ ℓ) (Fin.castAdd ℓ (Fin.natAdd k i)) =
              Fin.natAdd k (Fin.castAdd ℓ i) := by
            ext; rfl
          rw [hc]
          simp
      · have hc : Fin.cast (Nat.add_assoc k ℓ₀ ℓ) (Fin.natAdd (k + ℓ₀) u₂) =
            Fin.natAdd k (Fin.natAdd ℓ₀ u₂) := by
          ext; simp [Nat.add_assoc]
        rw [hc]
        simp
    rw [h_eq]
    exact hy
  · intro z hz
    have hmem := hQ_ext z hz
    have hQ_res := hQ (fun u : Fin (k + ℓ₀) => z (Fin.cast h.symm (Fin.castAdd ℓ u))) hmem
    have heq : (fun i : Fin k => z (Fin.cast h.symm (Fin.castAdd ℓ (Fin.castAdd ℓ₀ i)))) =
        (fun i : Fin k => z (Fin.cast h'.symm (Fin.castAdd (ℓ₀ + ℓ) i))) := by
      ext i
      congr 1
    rw [← heq]
    exact hQ_res

theorem solution {τ τ' : Type} [Fintype τ] [Fintype τ'] {ar : τ → ℕ} {ar' : τ' → ℕ}
    {D : Type} [Fintype D] [DecidableEq D]
    (𝒜 ℬ : RelStruct τ ar D) (𝒜' ℬ' : RelStruct τ' ar' D)
    (hΓ : IsPromiseFamily 𝒜 ℬ) (hΓ' : IsPromiseFamily 𝒜' ℬ')
    (hΓ'Γ : ∀ R' : τ', PPPDefinable 𝒜 ℬ (𝒜'.rel R') (ℬ'.rel R'))
    {k : ℕ} (P'' Q'' : Set (Fin k → D)) (hPQ'' : P'' ⊆ Q'')
    (hΓ''Γ' : PPPDefinable 𝒜' ℬ' P'' Q'') :
    PPPDefinable 𝒜 ℬ P'' Q'' := by
  rcases hΓ''Γ' with ⟨ℓ₀, Ψ₀, h₀, hP₀, hQ₀⟩
  have h_sym : ∀ s : τ' ⊕ Unit, PPPDefinable 𝒜 ℬ ((withEqual 𝒜').rel s) ((withEqual ℬ').rel s) := by
    rintro (R' | _)
    · exact hΓ'Γ R'
    · exact pppDefinable_withEqual_self 𝒜 ℬ (.inr ())
  have h_clauses : PPPDefinable 𝒜 ℬ
      {w : Fin (k + ℓ₀) → D | ∀ j ∈ (Finset.univ : Finset (Fin Ψ₀.m)),
        w ∘ (fun i => Fin.cast h₀ (Ψ₀.scope j i)) ∈ (withEqual 𝒜').rel (Ψ₀.sym j)}
      {w : Fin (k + ℓ₀) → D | ∀ j ∈ (Finset.univ : Finset (Fin Ψ₀.m)),
        w ∘ (fun i => Fin.cast h₀ (Ψ₀.scope j i)) ∈ (withEqual ℬ').rel (Ψ₀.sym j)} := by
    refine pppDefinable_biInter 𝒜 ℬ Finset.univ _ _ (fun j _ => ?_)
    exact pppDefinable_pullback 𝒜 ℬ (h_sym (Ψ₀.sym j)) (fun i => Fin.cast h₀ (Ψ₀.scope j i))
  refine pppDefinable_proj 𝒜 ℬ h_clauses ?_ ?_
  · intro x hx
    rcases hP₀ x hx with ⟨y₀, hy₀⟩
    refine ⟨y₀, fun j _ => hy₀ j⟩
  · intro z₀ hz₀
    have hsat : Satisfies Ψ₀ (withEqual ℬ') (fun v => z₀ (Fin.cast h₀ v)) :=
      fun j => hz₀ j (Finset.mem_univ j)
    have hres := hQ₀ (fun v => z₀ (Fin.cast h₀ v)) hsat
    simpa using hres
