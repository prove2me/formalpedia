-- Prove2me | solution 1 for SymBoolPCSP.Galois.proposition_6_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:12:59.546398+00:00
-- url     : https://prove2.me/submissions/b8abd5cf-883e-42ed-b00f-51b1a6626e02

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

theorem solution {τ : Type} [Fintype τ] {ar : τ → ℕ} {D : Type} [Fintype D]
    [DecidableEq D] (𝒜 ℬ : RelStruct τ ar D) (hΓ : IsPromiseFamily 𝒜 ℬ)
    (L : ℕ) (hL : 0 < L) (e : Fin (Fintype.card (Fin L → D)) ≃ (Fin L → D)) :
    PPPDefinable 𝒜 ℬ (asTuples e (SL 𝒜 L)) (asTuples e (TL 𝒜 ℬ L)) := by
  classical
  let N := Fintype.card (Fin L → D)
  let ι := Σ R : τ, (Fin L → Fin (ar R) → D)
  let P (p : ι) : Set (Fin N → D) :=
    {t | (∀ l, p.2 l ∈ 𝒜.rel p.1) → (fun c => t (e.symm (fun l => p.2 l c))) ∈ 𝒜.rel p.1}
  let Q (p : ι) : Set (Fin N → D) :=
    {t | (∀ l, p.2 l ∈ 𝒜.rel p.1) → (fun c => t (e.symm (fun l => p.2 l c))) ∈ ℬ.rel p.1}
  have h_inter : PPPDefinable 𝒜 ℬ
      {t : Fin N → D | ∀ p ∈ (Finset.univ : Finset ι), t ∈ P p}
      {t : Fin N → D | ∀ p ∈ (Finset.univ : Finset ι), t ∈ Q p} := by
    refine pppDefinable_biInter 𝒜 ℬ Finset.univ P Q (fun p _ => ?_)
    by_cases hM : ∀ l, p.2 l ∈ 𝒜.rel p.1
    · have hP_eq : P p =
          {t : Fin N → D | t ∘ (fun c => e.symm (fun l => p.2 l c)) ∈ (withEqual 𝒜).rel (.inl p.1)} := by
        ext t
        dsimp [P, N, withEqual, Function.comp_def]
        exact ⟨fun h => h hM, fun h _ => h⟩
      have hQ_eq : Q p =
          {t : Fin N → D | t ∘ (fun c => e.symm (fun l => p.2 l c)) ∈ (withEqual ℬ).rel (.inl p.1)} := by
        ext t
        dsimp [Q, N, withEqual, Function.comp_def]
        exact ⟨fun h => h hM, fun h _ => h⟩
      rw [hP_eq, hQ_eq]
      exact pppDefinable_pullback 𝒜 ℬ (pppDefinable_withEqual_self 𝒜 ℬ (.inl p.1))
        (fun c => e.symm (fun l => p.2 l c))
    · have hP_univ : P p = Set.univ := by
        ext t
        simp [P, hM]
      have hQ_univ : Q p = Set.univ := by
        ext t
        simp [Q, hM]
      rw [hP_univ, hQ_univ]
      exact pppDefinable_univ 𝒜 ℬ N
  have hS : {t : Fin N → D | ∀ p ∈ (Finset.univ : Finset ι), t ∈ P p} = asTuples e (SL 𝒜 L) := by
    ext t
    dsimp [P, ι, N, asTuples, SL, IsPolymorphism]
    exact ⟨fun h R M => h ⟨R, M⟩ (Finset.mem_univ _), fun h ⟨R, M⟩ _ => h R M⟩
  have hT : {t : Fin N → D | ∀ p ∈ (Finset.univ : Finset ι), t ∈ Q p} = asTuples e (TL 𝒜 ℬ L) := by
    ext t
    dsimp [Q, ι, N, asTuples, TL, IsPolymorphism]
    exact ⟨fun h R M => h ⟨R, M⟩ (Finset.mem_univ _), fun h ⟨R, M⟩ _ => h R M⟩
  rw [← hS, ← hT]
  exact h_inter
