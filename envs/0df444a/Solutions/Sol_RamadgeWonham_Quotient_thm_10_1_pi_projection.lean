-- Prove2me | solution 1 for RamadgeWonham.Quotient.thm_10_1_pi_projection
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:41:33.886976+00:00
-- url     : https://prove2.me/submissions/97a5bc8a-3294-4293-81eb-22cb6907acd7

import Definitions.Def_RamadgeWonham_Quotient_Recognizer
import Definitions.Def_RamadgeWonham_Quotient_Reduced
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

private theorem fold_none {α Q : Type} (δ : α → Q → Option Q) (s : List α) :
    s.foldl (fun o σ => o.bind (δ σ)) none=none := by
  induction s with
  | nil => rfl
  | cons σ s ih => exact ih

private theorem run_append {α : Type} (G : Shared.Generator α) (s t : List α) :
    G.run (s++t)=(G.run s).bind (fun q => G.runFrom q t) := by
  unfold Shared.Generator.run Shared.Generator.runFrom
  rw [List.foldl_append]
  cases h : s.foldl (fun o σ => o.bind (G.δ σ)) (some G.q0) with
  | none => exact fold_none G.δ t
  | some q => rfl

private theorem pre_generated {α : Type} {Ec : Set α} (G : Shared.Generator α) (S : Shared.Supervisor α Ec) :
    Shared.pre (Shared.Lsup G S)=Shared.Lsup G S := by
  ext s
  constructor
  · rintro ⟨t,ht⟩
    cases hs : Shared.clRun G S s with
    | none =>
      have hh : Shared.clRun G S (s++t)=none := by
        unfold Shared.clRun at hs ⊢
        rw [List.foldl_append,hs]
        exact fold_none (Shared.clStep G S) t
      change (Shared.clRun G S (s++t)).isSome at ht
      simp [hh] at ht
    | some q =>
      change (Shared.clRun G S s).isSome
      simp [hs]
  · intro hs
    exact ⟨[],by simpa using hs⟩

private theorem well_defined {α : Type} {Ec : Set α} (G : Shared.Generator α) (S : Shared.Supervisor α Ec)
    (hred : KReduced S.S (Shared.Lsup G S)) (R : Shared.Generator α)
    (hR : IsRecognizer R (Shared.Lsup G S)) (s t : List α)
    (hs : s∈Shared.Lsup G S) (ht : t∈Shared.Lsup G S) (he : R.run s=R.run t) : S.S.run s=S.S.run t := by
  apply hred s t
  · rw [pre_generated]; exact hs
  · rw [pre_generated]; exact ht
  · intro u
    rw [pre_generated,← hR.2]
    change (∃ q, R.run (s++u)=some q ∧ q∈R.Qm) ↔ (∃ q, R.run (t++u)=some q ∧ q∈R.Qm)
    rw [run_append,run_append,he]

private theorem recognizer_mem {α : Type} (R : Shared.Generator α) (K : Set (List α))
    (hR : IsRecognizer R K) (hmark : R.Qm=Set.univ) (s : List α) (q : R.Q) (hq : R.run s=some q) : s∈K := by
  rw [← hR.2]
  exact ⟨q,hq,by rw [hmark]; trivial⟩

private theorem exists_rec_projection {α : Type} {Ec : Set α} (G : Shared.Generator α) (S : Shared.Supervisor α Ec)
    (hred : KReduced S.S (Shared.Lsup G S)) (htrim : KTrim S.S (Shared.Lsup G S))
    (R : Shared.Generator α) (hR : IsRecognizer R (Shared.Lsup G S)) (hmark : R.Qm=Set.univ) :
    ∃ π : R.Q → S.S.Q,
      (∀ s∈Shared.Lsup G S, ∀ r : R.Q, R.run s=some r → S.S.run s=some (π r)) ∧
      IsProjection (ofRecognizer R (π ⁻¹' S.S.Qm) (fun r => S.φ (π r))) S π := by
  classical
  have hrep (r : R.Q) : ∃ s, s∈Shared.Lsup G S ∧ R.run s=some r := by
    obtain ⟨s,hs⟩ := hR.1 r
    exact ⟨s,recognizer_mem R _ hR hmark s r hs,hs⟩
  choose rep hrepk hrepe using hrep
  have hex (r : R.Q) : ∃ x, S.S.run (rep r)=some x := by
    obtain ⟨⟨x,q⟩,hx⟩ := Option.isSome_iff_exists.mp (hrepk r)
    exact ⟨x,(cl_components G S (rep r) x q hx).1⟩
  choose π hπrun using hex
  have hagree : ∀ s∈Shared.Lsup G S, ∀ r : R.Q, R.run s=some r → S.S.run s=some (π r) := by
    intro s hs r hr
    have he := well_defined G S hred R hR s (rep r) hs (hrepk r) (hr.trans (hrepe r).symm)
    exact he.trans (hπrun r)
  refine ⟨π,hagree,?_,?_,?_,?_⟩
  · intro x
    obtain ⟨s,hs,hx⟩ := htrim x
    rw [pre_generated] at hs
    have hRm : s∈R.Lm := by rw [hR.2]; exact hs
    obtain ⟨r,hr,hrmark⟩ := hRm
    exact ⟨r,Option.some.inj ((hagree s hs r hr).symm.trans hx)⟩
  · constructor
    · have hs : ([] : List α)∈Shared.Lsup G S := rfl
      have hh := hagree [] hs R.q0 rfl
      exact (Option.some.inj hh).symm
    · rfl
  · change ∀ (σ : α) (r r' : R.Q), R.δ σ r=some r' → S.S.δ σ (π r)=some (π r')
    intro σ r r' hstep
    have hr' : R.run (rep r++[σ])=some r' := by rw [run_snoc,hrepe]; exact hstep
    have hk' := recognizer_mem R _ hR hmark _ r' hr'
    have hs' := hagree _ hk' r' hr'
    rw [run_snoc,hπrun] at hs'
    exact hs'
  · intro r; rfl

private theorem recognizer_generated {α : Type} {Ec : Set α} (G : Shared.Generator α)
    (K : Set (List α)) (hclosed : Shared.pre K=K) (hKG : K⊆G.L)
    (R : Shared.Generator α) (hR : IsRecognizer R K) (hmark : R.Qm=Set.univ)
    (Xm : Set R.Q) (φ : R.Q → Ec → Bool)
    (hen : ∀ (σ : α) (x : R.Q), (∃ s, R.run s=some x ∧ s++[σ]∈K) → (ofRecognizer R Xm φ).enabled x σ) :
    Shared.Lsup G (ofRecognizer R Xm φ)=K := by
  let S0 := ofRecognizer R Xm φ
  have hf (s : List α) (hs : s∈Shared.Lsup G S0) : s∈K := by
    obtain ⟨⟨x,q⟩,hx⟩ := Option.isSome_iff_exists.mp hs
    have hr : R.run s=some x := (cl_components G S0 s x q hx).1
    exact recognizer_mem R K hR hmark s x hr
  ext s
  refine ⟨hf s,?_⟩
  induction s using List.reverseRecOn with
  | nil => intro h; exact rfl
  | append_singleton s σ ih =>
    intro hfull
    have hpre : s∈K := by rw [← hclosed]; exact ⟨[σ],hfull⟩
    have hsrc : s∈Shared.Lsup G S0 := ih hpre
    obtain ⟨p,hp⟩ : ∃ p : R.Q × G.Q, Shared.clRun G S0 s=some p := Option.isSome_iff_exists.mp hsrc
    rcases p with ⟨x,q⟩
    have hc := cl_components G S0 s x q hp
    have hr : R.run s=some x := hc.1
    have htarget : s++[σ]∈R.Lm := by rw [hR.2]; exact hfull
    obtain ⟨x',hx',hxm'⟩ := htarget
    obtain ⟨q',hq'⟩ := Option.isSome_iff_exists.mp (hKG hfull)
    have hrs : R.δ σ x=some x' := by rw [run_snoc,hr] at hx'; exact hx'
    have hgs : G.δ σ q=some q' := by rw [run_snoc,hc.2] at hq'; exact hq'
    apply Option.isSome_iff_exists.mpr
    refine ⟨(x',q'),?_⟩
    rw [cl_snoc,hp]
    apply (cl_step_iff G S0 σ x x' q q').mpr
    exact ⟨hen σ x ⟨s,hr,hfull⟩,hrs,hgs⟩

private theorem map_enabled {α : Type} {Ec : Set α} (R : Shared.Generator α) (S : Shared.Supervisor α Ec)
    (π : R.Q → S.S.Q) (x : R.Q) (σ : α) :
    (ofRecognizer R (π ⁻¹' S.S.Qm) (fun x => S.φ (π x))).enabled x σ ↔ S.enabled (π x) σ := Iff.rfl

private theorem rec_enabled {α : Type} {Ec : Set α} (G : Shared.Generator α) (S : Shared.Supervisor α Ec)
    (R : Shared.Generator α) (π : R.Q → S.S.Q)
    (hagree : ∀ s∈Shared.Lsup G S, ∀ x : R.Q, R.run s=some x → S.S.run s=some (π x)) :
    ∀ (σ : α) (x : R.Q), (∃ s, R.run s=some x ∧ s++[σ]∈Shared.Lsup G S) →
      (ofRecognizer R (π ⁻¹' S.S.Qm) (fun x => S.φ (π x))).enabled x σ := by
  intro σ x h
  obtain ⟨s,hs,hfull⟩ := h
  have hpre : s∈Shared.Lsup G S := by rw [← pre_generated G S]; exact ⟨[σ],hfull⟩
  obtain ⟨⟨y',q'⟩,hcl⟩ := Option.isSome_iff_exists.mp hfull
  rw [cl_snoc] at hcl
  obtain ⟨⟨y,q⟩,hprecl,hstep⟩ := Option.bind_eq_some_iff.mp hcl
  have hyrun := (cl_components G S s y q hprecl).1
  have hag := hagree s hpre x hs
  have hy : y=π x := Option.some.inj (hyrun.symm.trans hag)
  have he := ((cl_step_iff G S σ y y' q q').mp hstep).1
  rw [map_enabled]
  simpa only [← hy] using he

private theorem rec_complete {α : Type} {Ec : Set α} (G : Shared.Generator α) (S : Shared.Supervisor α Ec)
    (hS : Shared.Complete G S) (R : Shared.Generator α) (hR : IsRecognizer R (Shared.Lsup G S))
    (hmark : R.Qm=Set.univ) (π : R.Q → S.S.Q)
    (hagree : ∀ s∈Shared.Lsup G S, ∀ x : R.Q, R.run s=some x → S.S.run s=some (π x)) :
    Shared.Complete G (ofRecognizer R (π ⁻¹' S.S.Qm) (fun x => S.φ (π x))) := by
  let S0 := ofRecognizer R (π ⁻¹' S.S.Qm) (fun x => S.φ (π x))
  have hKG : Shared.Lsup G S⊆G.L := by
    intro s hs
    obtain ⟨⟨x,q⟩,hx⟩ := Option.isSome_iff_exists.mp hs
    exact Option.isSome_iff_exists.mpr ⟨q,(cl_components G S s x q hx).2⟩
  have heq : Shared.Lsup G S0=Shared.Lsup G S := recognizer_generated G _ (pre_generated G S) hKG R hR hmark _ _ (rec_enabled G S R π hagree)
  intro s σ hs hsg hen
  change s++[σ]∈Shared.Lsup G S0
  rw [heq]
  have hsk : s∈Shared.Lsup G S := by rw [← heq]; exact hs
  apply hS s σ hsk hsg
  intro y hy
  have hRm : s∈R.Lm := by rw [hR.2]; exact hsk
  obtain ⟨x,hx,hxm⟩ := hRm
  have hag := hagree s hsk x hx
  have he : π x=y := Option.some.inj (hag.symm.trans hy)
  have hxe := hen x hx
  change S.enabled (π x) σ at hxe
  simpa only [he] using hxe

open Shared.Generator

theorem solution
    {α : Type} [Fintype α] {Ec : Set α} (𝒢 : Shared.Generator α) (h𝒢 : 𝒢.L = Shared.pre 𝒢.Lm)
    (𝒮 : Shared.Supervisor α Ec) (h𝒮acc : 𝒮.S.Accessible) (h𝒮 : Shared.Complete 𝒢 𝒮)
    (hred : KReduced 𝒮.S (Shared.Lsup 𝒢 𝒮)) (htrim : KTrim 𝒮.S (Shared.Lsup 𝒢 𝒮))
    (R : Shared.Generator α) (hRrec : IsRecognizer R (Shared.Lsup 𝒢 𝒮)) (hRtrim : R.IsTrim)
    (hRQm : R.Qm = Set.univ) :
    ∃ π : R.Q → 𝒮.S.Q,
      (∀ s ∈ Shared.Lsup 𝒢 𝒮, ∀ x0 : R.Q, R.run s = some x0 → 𝒮.S.run s = some (π x0)) ∧
      IsProjection (ofRecognizer R (π ⁻¹' 𝒮.S.Qm) (fun x0 => 𝒮.φ (π x0))) 𝒮 π := by
  exact exists_rec_projection 𝒢 𝒮 hred htrim R hRrec hRQm
