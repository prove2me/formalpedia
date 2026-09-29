-- Prove2me | solution 1 for RamadgeWonham.Synthesis.smp_scp_solvable_iff_sup
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T20:08:11.058595+00:00
-- url     : https://prove2.me/submissions/1974af09-442b-402f-acdd-a16271c037cc

import Mathlib
import Definitions.Def_RamadgeWonham_Synthesis_Controllable
import Definitions.Def_RamadgeWonham_Synthesis_Problems

set_option autoImplicit false

/-! ## Basic facts on runs, prefixes and closed loops -/

open RamadgeWonham in
theorem rw4374_run_snoc {α : Type} (G : Shared.Generator α) (s : List α) (σ : α) :
    G.run (s ++ [σ]) = (G.run s).bind (G.δ σ) := by
  unfold Shared.Generator.run Shared.Generator.runFrom
  rw [List.foldl_append]
  rfl

open RamadgeWonham in
theorem rw4374_clRun_snoc {α : Type} {Ec : Set α} (G : Shared.Generator α)
    (𝒮 : Shared.Supervisor α Ec) (s : List α) (σ : α) :
    Shared.clRun G 𝒮 (s ++ [σ]) = (Shared.clRun G 𝒮 s).bind (Shared.clStep G 𝒮 σ) := by
  unfold Shared.clRun
  rw [List.foldl_append]
  rfl

open RamadgeWonham in
theorem rw4374_pre_prefix {α : Type} {K : Set (List α)} {s t : List α}
    (h : s ++ t ∈ Shared.pre K) : s ∈ Shared.pre K := by
  obtain ⟨u, hu⟩ := h
  exact ⟨t ++ u, by simpa [List.append_assoc] using hu⟩

open RamadgeWonham in
theorem rw4374_subset_pre {α : Type} {K : Set (List α)} : K ⊆ Shared.pre K :=
  fun s hs => ⟨[], by simpa using hs⟩

open RamadgeWonham in
theorem rw4374_pre_mono {α : Type} {A B : Set (List α)} (h : A ⊆ B) :
    Shared.pre A ⊆ Shared.pre B :=
  fun _ ⟨t, ht⟩ => ⟨t, h ht⟩

open RamadgeWonham in
theorem rw4374_pre_eq_of_between {α : Type} {A B : Set (List α)} (h1 : A ⊆ B)
    (h2 : B ⊆ Shared.pre A) : Shared.pre B = Shared.pre A := by
  apply Set.Subset.antisymm
  · intro s ⟨t, ht⟩
    obtain ⟨u, hu⟩ := h2 ht
    exact ⟨t ++ u, by simpa [List.append_assoc] using hu⟩
  · exact rw4374_pre_mono h1

open RamadgeWonham in
theorem rw4374_run_prefix {α : Type} (G : Shared.Generator α) (s t : List α)
    (h : (G.run (s ++ t)).isSome) : (G.run s).isSome := by
  induction t using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton t σ ih =>
    apply ih
    rw [← List.append_assoc, rw4374_run_snoc] at h
    cases hr : G.run (s ++ t) with
    | none => simp [hr] at h
    | some q => simp

open RamadgeWonham in
theorem rw4374_L_prefix {α : Type} {G : Shared.Generator α} {s t : List α}
    (h : s ++ t ∈ G.L) : s ∈ G.L := rw4374_run_prefix G s t h

open RamadgeWonham in
theorem rw4374_clRun_run {α : Type} {Ec : Set α} (G : Shared.Generator α)
    (𝒮 : Shared.Supervisor α Ec) (s : List α) (x : 𝒮.S.Q) (q : G.Q)
    (h : Shared.clRun G 𝒮 s = some (x, q)) : 𝒮.S.run s = some x ∧ G.run s = some q := by
  induction s using List.reverseRecOn generalizing x q with
  | nil =>
    simp only [Shared.clRun, List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | append_singleton s σ ih =>
    rw [rw4374_clRun_snoc] at h
    cases hc : Shared.clRun G 𝒮 s with
    | none => simp [hc] at h
    | some p =>
      obtain ⟨x0, q0⟩ := p
      rw [hc] at h
      obtain ⟨h1, h2⟩ := ih x0 q0 hc
      simp only [Option.bind_some] at h
      unfold Shared.clStep at h
      split_ifs at h with hen
      · cases hx : 𝒮.S.δ σ x0 with
        | none => simp [hx] at h
        | some x' =>
          cases hq : G.δ σ q0 with
          | none => simp [hx, hq] at h
          | some q' =>
            simp only [hx, hq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨?_, ?_⟩
            · rw [rw4374_run_snoc, h1]; exact hx
            · rw [rw4374_run_snoc, h2]; exact hq

open RamadgeWonham in
theorem rw4374_Lsup_subset_L {α : Type} {Ec : Set α} (G : Shared.Generator α)
    (𝒮 : Shared.Supervisor α Ec) : Shared.Lsup G 𝒮 ⊆ G.L := by
  intro s hs
  unfold Shared.Lsup at hs
  obtain ⟨⟨x, q⟩, hxq⟩ := Option.isSome_iff_exists.1 hs
  have := (rw4374_clRun_run G 𝒮 s x q hxq).2
  simp [Shared.Generator.L, this]

open RamadgeWonham in
theorem rw4374_Lmsup_subset_Lsup {α : Type} {Ec : Set α} (G : Shared.Generator α)
    (𝒮 : Shared.Supervisor α Ec) : Shared.Lmsup G 𝒮 ⊆ Shared.Lsup G 𝒮 := by
  rintro s ⟨x, q, h, -, -⟩
  simp [Shared.Lsup, h]

/-! ## Properness gives controllability of the marked / controlled language -/

open RamadgeWonham RamadgeWonham.Synthesis in
theorem rw4374_proper_Lmsup {α : Type} {Ec : Set α} (G : Shared.Generator α)
    (𝒮 : Shared.Supervisor α Ec) (hP : Shared.Proper G 𝒮) :
    Controllable G Ec (Shared.Lmsup G 𝒮) := by
  obtain ⟨hC, hNB, hNR⟩ := hP
  have hpre : Shared.pre (Shared.Lmsup G 𝒮) = Shared.Lsup G 𝒮 := by
    rw [← hNR]; exact hNB
  refine ⟨fun s hs => rw4374_Lsup_subset_L G 𝒮 (rw4374_Lmsup_subset_Lsup G 𝒮 hs), ?_⟩
  intro s σ hs hσ hsσ
  rw [hpre] at hs ⊢
  apply hC s σ hs hsσ
  intro x _ hσ'
  exact absurd hσ' hσ

open RamadgeWonham RamadgeWonham.Synthesis in
theorem rw4374_proper_Lcsup {α : Type} {Ec : Set α} (G : Shared.Generator α)
    (𝒮 : Shared.Supervisor α Ec) (hP : Shared.Proper G 𝒮) :
    Controllable G Ec (Shared.Lcsup G 𝒮) ∧
      Shared.Lcsup G 𝒮 = Shared.pre (Shared.Lcsup G 𝒮) ∩ G.Lm := by
  obtain ⟨hC, hNB, hNR⟩ := hP
  refine ⟨⟨fun s hs => rw4374_Lsup_subset_L G 𝒮 hs.1, ?_⟩, ?_⟩
  · intro s σ hs hσ hsσ
    rw [hNB] at hs ⊢
    apply hC s σ hs hsσ
    intro x _ hσ'
    exact absurd hσ' hσ
  · rw [hNB]; rfl

/-! ## Suprema of controllable languages -/

open RamadgeWonham RamadgeWonham.Synthesis in
theorem rw4374_sSup_C {α : Type} (G : Shared.Generator α) (Ec : Set α) (Lg : Set (List α))
    (𝒦 : Set (Set (List α))) (h : 𝒦 ⊆ Cset G Ec Lg) : sSup 𝒦 ∈ Cset G Ec Lg := by
  rw [Set.sSup_eq_sUnion]
  refine ⟨Set.sUnion_subset fun K hK => (h hK).1, ?_, ?_⟩
  · exact Set.sUnion_subset fun K hK => (h hK).2.1
  · intro s σ hs hσ hsσ
    obtain ⟨t, K, hK, hst⟩ := hs
    have hsK : s ∈ Shared.pre K := ⟨t, hst⟩
    obtain ⟨u, hu⟩ := (h hK).2.2 s σ hsK hσ hsσ
    exact ⟨u, K, hK, hu⟩

open RamadgeWonham RamadgeWonham.Synthesis in
theorem rw4374_sSup_CF {α : Type} (G : Shared.Generator α) (Ec : Set α) (Lg : Set (List α))
    (𝒦 : Set (Set (List α))) (h : 𝒦 ⊆ Cset G Ec Lg ∩ Fset G Lg) :
    sSup 𝒦 ∈ Cset G Ec Lg ∩ Fset G Lg := by
  refine ⟨rw4374_sSup_C G Ec Lg 𝒦 (fun K hK => (h hK).1), ?_⟩
  have hF : ∀ K ∈ 𝒦, K ⊆ Lg ∧ K = Shared.pre K ∩ G.Lm := fun K hK => (h hK).2
  rw [Set.sSup_eq_sUnion]
  refine ⟨Set.sUnion_subset fun K hK => (hF K hK).1, ?_⟩
  apply Set.Subset.antisymm
  · rintro s ⟨K, hK, hs⟩
    have := (hF K hK).2 ▸ hs
    exact ⟨⟨[], K, hK, by simpa using hs⟩, this.2⟩
  · rintro s ⟨⟨t, K, hK, hst⟩, hsL⟩
    have hsK : s ∈ Shared.pre K := ⟨t, hst⟩
    have : s ∈ K := by rw [(hF K hK).2]; exact ⟨hsK, hsL⟩
    exact ⟨K, hK, this⟩

/-! ## The canonical supervisor realizing a controllable language -/

open RamadgeWonham in
open Classical in
noncomputable def rw4374_mk {α : Type} (Ec : Set α) (K : Set (List α)) (hne : K.Nonempty) :
    Shared.Supervisor α Ec where
  S :=
    { Q := {w : List α // w ∈ Shared.pre K}
      δ := fun σ x => if h : x.1 ++ [σ] ∈ Shared.pre K then some ⟨x.1 ++ [σ], h⟩ else none
      q0 := ⟨[], by obtain ⟨k, hk⟩ := hne; exact ⟨k, by simpa using hk⟩⟩
      Qm := {x | x.1 ∈ K} }
  φ := fun x σ => decide (x.1 ++ [σ.1] ∈ Shared.pre K)

open RamadgeWonham in
theorem rw4374_mk_δ_pos {α : Type} (Ec : Set α) (K : Set (List α)) (hne : K.Nonempty)
    (x : {w : List α // w ∈ Shared.pre K}) (σ : α) (h : x.1 ++ [σ] ∈ Shared.pre K) :
    (rw4374_mk Ec K hne).S.δ σ x = some ⟨x.1 ++ [σ], h⟩ := by
  simp [rw4374_mk, h]

open RamadgeWonham in
theorem rw4374_mk_δ_neg {α : Type} (Ec : Set α) (K : Set (List α)) (hne : K.Nonempty)
    (x : {w : List α // w ∈ Shared.pre K}) (σ : α) (h : x.1 ++ [σ] ∉ Shared.pre K) :
    (rw4374_mk Ec K hne).S.δ σ x = none := by
  simp [rw4374_mk, h]

open RamadgeWonham in
theorem rw4374_mk_φ {α : Type} (Ec : Set α) (K : Set (List α)) (hne : K.Nonempty)
    (x : {w : List α // w ∈ Shared.pre K}) (σ : Ec) :
    (rw4374_mk Ec K hne).φ x σ = true ↔ x.1 ++ [σ.1] ∈ Shared.pre K := by
  simp [rw4374_mk]

open RamadgeWonham in
theorem rw4374_mk_run {α : Type} (Ec : Set α) (K : Set (List α)) (hne : K.Nonempty)
    (s : List α) (h : s ∈ Shared.pre K) :
    (rw4374_mk Ec K hne).S.run s = some ⟨s, h⟩ := by
  induction s using List.reverseRecOn with
  | nil => rfl
  | append_singleton s σ ih =>
    have hs : s ∈ Shared.pre K := rw4374_pre_prefix (t := [σ]) h
    rw [rw4374_run_snoc, ih hs]
    exact rw4374_mk_δ_pos Ec K hne ⟨s, hs⟩ σ h

open RamadgeWonham in
theorem rw4374_mk_run_mem {α : Type} (Ec : Set α) (K : Set (List α)) (hne : K.Nonempty)
    (s : List α) (x : {w : List α // w ∈ Shared.pre K})
    (h : (rw4374_mk Ec K hne).S.run s = some x) : s ∈ Shared.pre K ∧ x.1 = s := by
  induction s using List.reverseRecOn generalizing x with
  | nil =>
    have h0 : (rw4374_mk Ec K hne).S.run [] = some (rw4374_mk Ec K hne).S.q0 := rfl
    rw [h0] at h
    have hx : (rw4374_mk Ec K hne).S.q0 = x := Option.some.inj h
    have hv : ([] : List α) = x.1 :=
      congrArg (fun y : {w : List α // w ∈ Shared.pre K} => y.1) hx
    exact ⟨by rw [hv]; exact x.2, hv.symm⟩
  | append_singleton s σ ih =>
    rw [rw4374_run_snoc] at h
    cases hr : (rw4374_mk Ec K hne).S.run s with
    | none => simp [hr] at h
    | some x0 =>
      rw [hr] at h
      simp only [Option.bind_some] at h
      obtain ⟨-, h0⟩ := ih x0 hr
      by_cases hp : x0.1 ++ [σ] ∈ Shared.pre K
      · rw [rw4374_mk_δ_pos Ec K hne x0 σ hp] at h
        have hx : (⟨x0.1 ++ [σ], hp⟩ : {w : List α // w ∈ Shared.pre K}) = x := Option.some.inj h
        subst hx
        exact ⟨by rw [← h0]; exact hp, by simp [h0]⟩
      · rw [rw4374_mk_δ_neg Ec K hne x0 σ hp] at h
        simp at h

open RamadgeWonham RamadgeWonham.Synthesis in
theorem rw4374_mk_clRun {α : Type} (G : Shared.Generator α) (Ec : Set α) (K : Set (List α))
    (hne : K.Nonempty) (s : List α) (h : s ∈ Shared.pre K) (q : G.Q) (hq : G.run s = some q) :
    Shared.clRun G (rw4374_mk Ec K hne) s = some (⟨s, h⟩, q) := by
  induction s using List.reverseRecOn generalizing q with
  | nil =>
    have h0 : G.run [] = some G.q0 := rfl
    rw [h0] at hq
    have hq0 : G.q0 = q := Option.some.inj hq
    subst hq0
    rfl
  | append_singleton s σ ih =>
    have hs : s ∈ Shared.pre K := rw4374_pre_prefix (t := [σ]) h
    rw [rw4374_run_snoc] at hq
    cases hr : G.run s with
    | none => simp [hr] at hq
    | some q0 =>
      rw [hr] at hq
      simp only [Option.bind_some] at hq
      have h1 := ih hs q0 hr
      rw [rw4374_clRun_snoc, h1]
      simp only [Option.bind_some]
      unfold Shared.clStep
      have hen : (rw4374_mk Ec K hne).enabled ⟨s, hs⟩ σ := by
        intro hσ
        exact (rw4374_mk_φ Ec K hne ⟨s, hs⟩ ⟨σ, hσ⟩).2 h
      rw [if_pos hen]
      simp only []
      rw [rw4374_mk_δ_pos Ec K hne ⟨s, hs⟩ σ h, hq]

open RamadgeWonham in
theorem rw4374_Lm_subset_L {α : Type} (G : Shared.Generator α) : G.Lm ⊆ G.L := by
  rintro s ⟨q, hq, -⟩
  simp [Shared.Generator.L, hq]

open RamadgeWonham RamadgeWonham.Synthesis in
theorem rw4374_exists_sup {α : Type} (G : Shared.Generator α) (Ec : Set α) (K : Set (List α))
    (hne : K.Nonempty) (hKG : K ⊆ G.Lm) (hU : UInvariant Ec G.L K) :
    ∃ 𝒮 : Shared.Supervisor α Ec, 𝒮.S.Accessible ∧ Shared.Complete G 𝒮 ∧
      Shared.Lsup G 𝒮 = Shared.pre K ∧ Shared.Lmsup G 𝒮 = K := by
  have hLsup : Shared.Lsup G (rw4374_mk Ec K hne) = Shared.pre K := by
    apply Set.Subset.antisymm
    · intro s hs
      unfold Shared.Lsup at hs
      obtain ⟨⟨x, q⟩, hxq⟩ := Option.isSome_iff_exists.1 hs
      exact (rw4374_mk_run_mem Ec K hne s x (rw4374_clRun_run G _ s x q hxq).1).1
    · intro s hs
      have hsL : s ∈ G.L := by
        obtain ⟨t, ht⟩ := hs
        exact rw4374_L_prefix (rw4374_Lm_subset_L G (hKG ht))
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hsL
      have := rw4374_mk_clRun G Ec K hne s hs q hq
      show (Shared.clRun G (rw4374_mk Ec K hne) s).isSome = true
      rw [this]; rfl
  have hLmsup : Shared.Lmsup G (rw4374_mk Ec K hne) = K := by
    apply Set.Subset.antisymm
    · rintro s ⟨x, q, h, hx, -⟩
      have := (rw4374_mk_run_mem Ec K hne s x (rw4374_clRun_run G _ s x q h).1).2
      rw [← this]; exact hx
    · intro s hs
      have hs' : s ∈ Shared.pre K := rw4374_subset_pre hs
      obtain ⟨q, hq, hqm⟩ := hKG hs
      exact ⟨⟨s, hs'⟩, q, rw4374_mk_clRun G Ec K hne s hs' q hq, hs, hqm⟩
  refine ⟨rw4374_mk Ec K hne, ?_, ?_, hLsup, hLmsup⟩
  · intro x
    exact ⟨x.1, rw4374_mk_run Ec K hne x.1 x.2⟩
  · intro s σ hs hsσ hen
    rw [hLsup] at hs ⊢
    have hen' := hen ⟨s, hs⟩ (rw4374_mk_run Ec K hne s hs)
    by_cases hσ : σ ∈ Ec
    · exact (rw4374_mk_φ Ec K hne ⟨s, hs⟩ ⟨σ, hσ⟩).1 (hen' hσ)
    · exact hU s σ hs hσ hsσ

open RamadgeWonham RamadgeWonham.Synthesis in
theorem rw4374_proper_of_sup {α : Type} {Ec : Set α} (G : Shared.Generator α)
    (𝒮 : Shared.Supervisor α Ec) (K : Set (List α)) (hKG : K ⊆ G.Lm)
    (hC : Shared.Complete G 𝒮) (hL : Shared.Lsup G 𝒮 = Shared.pre K)
    (hM : Shared.Lmsup G 𝒮 = K) :
    Shared.Proper G 𝒮 ∧ K ⊆ Shared.Lcsup G 𝒮 ∧ Shared.Lcsup G 𝒮 ⊆ Shared.pre K := by
  have h1 : K ⊆ Shared.Lcsup G 𝒮 := fun k hk =>
    ⟨by rw [hL]; exact rw4374_subset_pre hk, hKG hk⟩
  have h2 : Shared.Lcsup G 𝒮 ⊆ Shared.pre K := fun s hs => by rw [← hL]; exact hs.1
  have h3 : Shared.pre (Shared.Lcsup G 𝒮) = Shared.pre K := rw4374_pre_eq_of_between h1 h2
  refine ⟨⟨hC, ?_, ?_⟩, h1, h2⟩
  · show Shared.pre (Shared.Lcsup G 𝒮) = Shared.Lsup G 𝒮
    rw [h3, hL]
  · show Shared.pre (Shared.Lcsup G 𝒮) = Shared.pre (Shared.Lmsup G 𝒮)
    rw [h3, hM]

theorem rw4374_le_sSup {α : Type} {𝒦 : Set (Set (List α))} {K : Set (List α)} (hK : K ∈ 𝒦) :
    K ⊆ sSup 𝒦 := by
  rw [Set.sSup_eq_sUnion]
  exact Set.subset_sUnion_of_mem hK

/-! ## The two halves of the theorem -/

open RamadgeWonham RamadgeWonham.Synthesis in
theorem rw4374_smp {α : Type} (G : Shared.Generator α) (Ec : Set α) (La Lg : Set (List α))
    (hLa : La.Nonempty) (hLaLg : La ⊆ Lg) (hLg : Lg ⊆ G.Lm) :
    ((∃ 𝒮 : Shared.Supervisor α Ec, SolvesSMP G La Lg 𝒮) ↔ La ⊆ sSup (Cset G Ec Lg)) ∧
      (La ⊆ sSup (Cset G Ec Lg) →
        ∃ 𝒮 : Shared.Supervisor α Ec, SolvesSMP G La Lg 𝒮 ∧ Shared.Lmsup G 𝒮 = sSup (Cset G Ec Lg) ∧
          ∀ 𝒮' : Shared.Supervisor α Ec, 𝒮'.S.Accessible → Shared.Proper G 𝒮' → Shared.Lmsup G 𝒮' ⊆ Lg →
            Shared.Lmsup G 𝒮' ⊆ Shared.Lmsup G 𝒮) := by
  have hmem : sSup (Cset G Ec Lg) ∈ Cset G Ec Lg :=
    rw4374_sSup_C G Ec Lg _ (fun K hK => hK)
  have hmin : ∀ 𝒮' : Shared.Supervisor α Ec, Shared.Proper G 𝒮' → Shared.Lmsup G 𝒮' ⊆ Lg →
      Shared.Lmsup G 𝒮' ⊆ sSup (Cset G Ec Lg) :=
    fun 𝒮' hP hLg' => rw4374_le_sSup ⟨hLg', rw4374_proper_Lmsup G 𝒮' hP⟩
  have build : La ⊆ sSup (Cset G Ec Lg) →
      ∃ 𝒮 : Shared.Supervisor α Ec, SolvesSMP G La Lg 𝒮 ∧
        Shared.Lmsup G 𝒮 = sSup (Cset G Ec Lg) := by
    intro h
    obtain ⟨k, hk⟩ := hLa
    have hne : (sSup (Cset G Ec Lg)).Nonempty := ⟨k, h hk⟩
    obtain ⟨𝒮, hacc, hC, hL, hM⟩ :=
      rw4374_exists_sup G Ec _ hne (hmem.1.trans hLg) hmem.2.2
    obtain ⟨hP, -, -⟩ := rw4374_proper_of_sup G 𝒮 _ (hmem.1.trans hLg) hC hL hM
    refine ⟨𝒮, ⟨hacc, hP, ?_, ?_⟩, hM⟩
    · rw [hM]; exact h
    · rw [hM]; exact hmem.1
  refine ⟨⟨?_, fun h => (build h).elim fun 𝒮 h' => ⟨𝒮, h'.1⟩⟩, ?_⟩
  · rintro ⟨𝒮, hacc, hP, hLa', hLg'⟩ 
    exact hLa'.trans (hmin 𝒮 hP hLg')
  · intro h
    obtain ⟨𝒮, hS, hM⟩ := build h
    refine ⟨𝒮, hS, hM, fun 𝒮' _ hP hLg' => ?_⟩
    rw [hM]; exact hmin 𝒮' hP hLg'

open RamadgeWonham RamadgeWonham.Synthesis in
theorem rw4374_scp {α : Type} (G : Shared.Generator α) (Ec : Set α) (La Lg : Set (List α))
    (hLa : La.Nonempty) (hLaLg : La ⊆ Lg) (hLg : Lg ⊆ G.Lm) :
    (((∃ 𝒮 : Shared.Supervisor α Ec, SolvesSCP G La Lg 𝒮) ↔
        La ⊆ sSup (Cset G Ec Lg ∩ Fset G Lg)) ∧
      (La ⊆ sSup (Cset G Ec Lg ∩ Fset G Lg) →
        ∃ 𝒮 : Shared.Supervisor α Ec, SolvesSCP G La Lg 𝒮 ∧
          Shared.Lcsup G 𝒮 = sSup (Cset G Ec Lg ∩ Fset G Lg) ∧
          ∀ 𝒮' : Shared.Supervisor α Ec, 𝒮'.S.Accessible → Shared.Proper G 𝒮' → Shared.Lcsup G 𝒮' ⊆ Lg →
            Shared.Lcsup G 𝒮' ⊆ Shared.Lcsup G 𝒮)) := by
  have hmem : sSup (Cset G Ec Lg ∩ Fset G Lg) ∈ Cset G Ec Lg ∩ Fset G Lg :=
    rw4374_sSup_CF G Ec Lg _ (fun K hK => hK)
  have hmin : ∀ 𝒮' : Shared.Supervisor α Ec, Shared.Proper G 𝒮' → Shared.Lcsup G 𝒮' ⊆ Lg →
      Shared.Lcsup G 𝒮' ⊆ sSup (Cset G Ec Lg ∩ Fset G Lg) := by
    intro 𝒮' hP hLg'
    obtain ⟨hct, hF⟩ := rw4374_proper_Lcsup G 𝒮' hP
    exact rw4374_le_sSup ⟨⟨hLg', hct⟩, ⟨hLg', hF⟩⟩
  have build : La ⊆ sSup (Cset G Ec Lg ∩ Fset G Lg) →
      ∃ 𝒮 : Shared.Supervisor α Ec, SolvesSCP G La Lg 𝒮 ∧
        Shared.Lcsup G 𝒮 = sSup (Cset G Ec Lg ∩ Fset G Lg) := by
    intro h
    obtain ⟨k, hk⟩ := hLa
    have hne : (sSup (Cset G Ec Lg ∩ Fset G Lg)).Nonempty := ⟨k, h hk⟩
    have hKG : sSup (Cset G Ec Lg ∩ Fset G Lg) ⊆ G.Lm := hmem.1.1.trans hLg
    obtain ⟨𝒮, hacc, hC, hL, hM⟩ := rw4374_exists_sup G Ec _ hne hKG hmem.1.2.2
    obtain ⟨hP, h1, h2⟩ := rw4374_proper_of_sup G 𝒮 _ hKG hC hL hM
    have hEq : Shared.Lcsup G 𝒮 = sSup (Cset G Ec Lg ∩ Fset G Lg) := by
      apply Set.Subset.antisymm _ h1
      intro s hs
      rw [hmem.2.2]
      exact ⟨h2 hs, hs.2⟩
    refine ⟨𝒮, ⟨hacc, hP, ?_, ?_⟩, hEq⟩
    · rw [hEq]; exact h
    · rw [hEq]; exact hmem.1.1
  refine ⟨⟨?_, fun h => (build h).elim fun 𝒮 h' => ⟨𝒮, h'.1⟩⟩, ?_⟩
  · rintro ⟨𝒮, hacc, hP, hLa', hLg'⟩
    exact hLa'.trans (hmin 𝒮 hP hLg')
  · intro h
    obtain ⟨𝒮, hS, hM⟩ := build h
    refine ⟨𝒮, hS, hM, fun 𝒮' _ hP hLg' => ?_⟩
    rw [hM]; exact hmin 𝒮' hP hLg'

/-! ## The theorem -/

open RamadgeWonham RamadgeWonham.Synthesis in
theorem solution {α : Type} [Fintype α] (G : Shared.Generator α) (Ec : Set α)
    (hG : G.L = Shared.pre G.Lm) (La Lg : Set (List α))
    (hLa : La.Nonempty) (hLaLg : La ⊆ Lg) (hLg : Lg ⊆ G.Lm) :
    (((∃ 𝒮 : Shared.Supervisor α Ec, SolvesSMP G La Lg 𝒮) ↔ La ⊆ sSup (Cset G Ec Lg)) ∧
      (La ⊆ sSup (Cset G Ec Lg) →
        ∃ 𝒮 : Shared.Supervisor α Ec, SolvesSMP G La Lg 𝒮 ∧ Shared.Lmsup G 𝒮 = sSup (Cset G Ec Lg) ∧
          ∀ 𝒮' : Shared.Supervisor α Ec, 𝒮'.S.Accessible → Shared.Proper G 𝒮' → Shared.Lmsup G 𝒮' ⊆ Lg →
            Shared.Lmsup G 𝒮' ⊆ Shared.Lmsup G 𝒮)) ∧
    (((∃ 𝒮 : Shared.Supervisor α Ec, SolvesSCP G La Lg 𝒮) ↔
        La ⊆ sSup (Cset G Ec Lg ∩ Fset G Lg)) ∧
      (La ⊆ sSup (Cset G Ec Lg ∩ Fset G Lg) →
        ∃ 𝒮 : Shared.Supervisor α Ec, SolvesSCP G La Lg 𝒮 ∧
          Shared.Lcsup G 𝒮 = sSup (Cset G Ec Lg ∩ Fset G Lg) ∧
          ∀ 𝒮' : Shared.Supervisor α Ec, 𝒮'.S.Accessible → Shared.Proper G 𝒮' → Shared.Lcsup G 𝒮' ⊆ Lg →
            Shared.Lcsup G 𝒮' ⊆ Shared.Lcsup G 𝒮)) := by
  exact ⟨rw4374_smp G Ec La Lg hLa hLaLg hLg, rw4374_scp G Ec La Lg hLa hLaLg hLg⟩
