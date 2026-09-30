-- Prove2me | solution 1 for RamadgeWonham.Quotient.prop_8_1_iii
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:31:29.479022+00:00
-- url     : https://prove2.me/submissions/f723c977-25bd-4331-b59e-363b507d9d8a

import Definitions.Def_RamadgeWonham_Quotient_Projection
import Mathlib.Tactic
set_option autoImplicit false
open RamadgeWonham RamadgeWonham.Quotient

private theorem run_snoc {α : Type} (G : Shared.Generator α) (s : List α) (σ : α) :
    G.run (s++[σ])=(G.run s).bind (G.δ σ) := by
  simp [Shared.Generator.run,Shared.Generator.runFrom,List.foldl_append]

private theorem projection_run {α : Type} {Ec : Set α} (S Sh : Shared.Supervisor α Ec)
    (π : S.S.Q → Sh.S.Q) (hπ : IsProjection S Sh π) (s : List α) :
    ∀ q, S.S.run s=some q → Sh.S.run s=some (π q) := by
  induction s using List.reverseRecOn with
  | nil =>
    intro q hq
    have he : S.S.q0=q := Option.some.inj hq
    subst q
    change some Sh.S.q0=some (π S.S.q0)
    rw [hπ.2.1.1]
  | append_singleton s σ ih =>
    intro q hq
    rw [run_snoc] at hq
    obtain ⟨r,hr,hrq⟩ := Option.bind_eq_some_iff.mp hq
    rw [run_snoc,ih r hr]
    exact hπ.2.2.1 σ r q hrq


private theorem cl_snoc {α : Type} {Ec : Set α} (G : Shared.Generator α) (S : Shared.Supervisor α Ec)
    (s : List α) (σ : α) : Shared.clRun G S (s++[σ])=(Shared.clRun G S s).bind (Shared.clStep G S σ) := by
  simp [Shared.clRun,List.foldl_append]

private theorem cl_step_iff {α : Type} {Ec : Set α} (G : Shared.Generator α) (S : Shared.Supervisor α Ec)
    (σ : α) (x x' : S.S.Q) (q q' : G.Q) :
    Shared.clStep G S σ (x,q)=some (x',q') ↔ S.enabled x σ ∧ S.S.δ σ x=some x' ∧ G.δ σ q=some q' := by
  classical
  by_cases he : S.enabled x σ
  · cases hx : S.S.δ σ x <;> cases hq : G.δ σ q <;> simp [Shared.clStep,he,hx,hq]
  · simp [Shared.clStep,he]

private theorem cl_components {α : Type} {Ec : Set α} (G : Shared.Generator α) (S : Shared.Supervisor α Ec)
    (s : List α) : ∀ x q, Shared.clRun G S s=some (x,q) → S.S.run s=some x ∧ G.run s=some q := by
  induction s using List.reverseRecOn with
  | nil =>
    intro x q h
    have he : (S.S.q0,G.q0)=(x,q) := Option.some.inj h
    cases he
    exact ⟨rfl,rfl⟩
  | append_singleton s σ ih =>
    intro x q h
    rw [cl_snoc] at h
    obtain ⟨⟨y,r⟩,hy,hh⟩ := Option.bind_eq_some_iff.mp h
    have hstep := (cl_step_iff G S σ y x r q).mp hh
    obtain ⟨hs,hg⟩ := ih y r hy
    rw [run_snoc,run_snoc,hs,hg]
    exact ⟨hstep.2.1,hstep.2.2⟩

private theorem projection_enabled {α : Type} {Ec : Set α} (S Sh : Shared.Supervisor α Ec)
    (π : S.S.Q → Sh.S.Q) (hπ : IsProjection S Sh π) (x : S.S.Q) (σ : α) :
    Sh.enabled (π x) σ ↔ S.enabled x σ := by
  simp only [Shared.Supervisor.enabled,hπ.2.2.2 x]

private theorem cl_projection {α : Type} {Ec : Set α} (G : Shared.Generator α) (S Sh : Shared.Supervisor α Ec)
    (π : S.S.Q → Sh.S.Q) (hπ : IsProjection S Sh π) (s : List α) :
    ∀ x q, Shared.clRun G S s=some (x,q) → Shared.clRun G Sh s=some (π x,q) := by
  induction s using List.reverseRecOn with
  | nil =>
    intro x q h
    have he : (S.S.q0,G.q0)=(x,q) := Option.some.inj h
    cases he
    change some (Sh.S.q0,G.q0)=some (π S.S.q0,G.q0)
    rw [hπ.2.1.1]
  | append_singleton s σ ih =>
    intro x q h
    rw [cl_snoc] at h
    obtain ⟨⟨y,r⟩,hy,hh⟩ := Option.bind_eq_some_iff.mp h
    have hstep := (cl_step_iff G S σ y x r q).mp hh
    rw [cl_snoc,ih y r hy]
    apply (cl_step_iff G Sh σ (π y) (π x) r q).mpr
    exact ⟨(projection_enabled S Sh π hπ y σ).mpr hstep.1,hπ.2.2.1 σ y x hstep.2.1,hstep.2.2⟩

private theorem generated_eq {α : Type} {Ec : Set α} (G : Shared.Generator α) (S Sh : Shared.Supervisor α Ec)
    (hS : Shared.Complete G S) (π : S.S.Q → Sh.S.Q) (hπ : IsProjection S Sh π) :
    Shared.Lsup G S=Shared.Lsup G Sh := by
  have forward (s : List α) (hs : s∈Shared.Lsup G S) : s∈Shared.Lsup G Sh := by
    obtain ⟨⟨x,q⟩,hx⟩ := Option.isSome_iff_exists.mp hs
    exact Option.isSome_iff_exists.mpr ⟨(π x,q),cl_projection G S Sh π hπ s x q hx⟩
  ext s
  refine ⟨forward s,?_⟩
  induction s using List.reverseRecOn with
  | nil => intro h; exact rfl
  | append_singleton s σ ih =>
    intro hs
    obtain ⟨⟨xh',q'⟩,hfull⟩ := Option.isSome_iff_exists.mp hs
    have hgfull := (cl_components G Sh (s++[σ]) xh' q' hfull).2
    rw [cl_snoc] at hfull
    obtain ⟨⟨xh,q⟩,hpre,hstep⟩ := Option.bind_eq_some_iff.mp hfull
    have hss : s∈Shared.Lsup G S := ih (Option.isSome_iff_exists.mpr ⟨(xh,q),hpre⟩)
    obtain ⟨⟨x,r⟩,hx⟩ := Option.isSome_iff_exists.mp hss
    have hxmap := cl_projection G S Sh π hπ s x r hx
    have he : (π x,r)=(xh,q) := Option.some.inj (hxmap.symm.trans hpre)
    have hxhe : π x=xh := congrArg Prod.fst he
    have hen : S.enabled x σ := by
      apply (projection_enabled S Sh π hπ x σ).mp
      rw [hxhe]
      exact ((cl_step_iff G Sh σ xh xh' q q').mp hstep).1
    apply hS s σ hss (Option.isSome_iff_exists.mpr ⟨q',hgfull⟩)
    intro y hy
    have hcomp := (cl_components G S s x r hx).1
    have hxy : x=y := Option.some.inj (hcomp.symm.trans hy)
    simpa only [← hxy] using hen

private theorem marked_eq {α : Type} {Ec : Set α} (G : Shared.Generator α) (S Sh : Shared.Supervisor α Ec)
    (hS : Shared.Complete G S) (π : S.S.Q → Sh.S.Q) (hπ : IsProjection S Sh π) :
    Shared.Lmsup G S=Shared.Lmsup G Sh := by
  ext s
  constructor
  · rintro ⟨x,q,hx,hm,hq⟩
    refine ⟨π x,q,cl_projection G S Sh π hπ s x q hx,?_,hq⟩
    rwa [hπ.2.1.2] at hm
  · rintro ⟨xh,q,hxh,hm,hq⟩
    have hs : s∈Shared.Lsup G S := by
      rw [generated_eq G S Sh hS π hπ]
      exact Option.isSome_iff_exists.mpr ⟨(xh,q),hxh⟩
    obtain ⟨⟨x,r⟩,hx⟩ := Option.isSome_iff_exists.mp hs
    have hxmap := cl_projection G S Sh π hπ s x r hx
    have he : (π x,r)=(xh,q) := Option.some.inj (hxmap.symm.trans hxh)
    have he1 : π x=xh := congrArg Prod.fst he
    have he2 : r=q := congrArg Prod.snd he
    subst r
    refine ⟨x,q,hx,?_,hq⟩
    rw [hπ.2.1.2]
    change π x∈Sh.S.Qm
    simpa only [he1] using hm

private theorem complete_projection {α : Type} {Ec : Set α} (G : Shared.Generator α) (S Sh : Shared.Supervisor α Ec)
    (hS : Shared.Complete G S) (π : S.S.Q → Sh.S.Q) (hπ : IsProjection S Sh π) : Shared.Complete G Sh := by
  intro s σ hs hsg hen
  have heq := generated_eq G S Sh hS π hπ
  rw [← heq] at hs ⊢
  obtain ⟨⟨x,q⟩,hx⟩ := Option.isSome_iff_exists.mp hs
  apply hS s σ hs hsg
  intro y hy
  have hrun := projection_run S Sh π hπ s y hy
  exact (projection_enabled S Sh π hπ y σ).mp (hen (π y) hrun)

theorem solution
    {α : Type} [Fintype α] {Ec : Set α} (𝒢 : Shared.Generator α) (h𝒢 : 𝒢.L = Shared.pre 𝒢.Lm)
    (𝒮 𝒮h : Shared.Supervisor α Ec) (h𝒮acc : 𝒮.S.Accessible) (h𝒮hacc : 𝒮h.S.Accessible)
    (h𝒮 : Shared.Complete 𝒢 𝒮)
    (π : 𝒮.S.Q → 𝒮h.S.Q) (hπ : IsProjection 𝒮 𝒮h π) :
    Shared.Complete 𝒢 𝒮h := by
  exact complete_projection 𝒢 𝒮 𝒮h h𝒮 π hπ
