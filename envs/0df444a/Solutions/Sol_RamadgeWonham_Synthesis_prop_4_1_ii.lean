-- Prove2me | solution 1 for RamadgeWonham.Synthesis.prop_4_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:47:29.405564+00:00
-- url     : https://prove2.me/submissions/4a61e862-a091-489a-9d33-81e603e27047

import Definitions.Def_RamadgeWonham_Quotient_Recognizer
import Definitions.Def_RamadgeWonham_Synthesis_Controllable
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

open RamadgeWonham.Synthesis

private noncomputable def history {α : Type} (Ec : Set α) (L K : Set (List α)) : Shared.Supervisor α Ec := by
  classical
  exact ⟨⟨List α, fun σ s => some (s++[σ]), [], K⟩,
    fun s σ => decide (s++[σ.val]∈L)⟩

private theorem history_run {α : Type} (Ec : Set α) (L K : Set (List α)) (s : List α) :
    (history Ec L K).S.run s=some s := by
  induction s using List.reverseRecOn with
  | nil => rfl
  | append_singleton s σ ih => rw [run_snoc,ih]; rfl

private theorem history_accessible {α : Type} (Ec : Set α) (L K : Set (List α)) :
    (history Ec L K).S.Accessible := fun s => ⟨s,history_run Ec L K s⟩

private theorem history_enabled {α : Type} (Ec : Set α) (L K : Set (List α)) (s : List α) (σ : α) :
    (history Ec L K).enabled s σ ↔ (σ∈Ec → s++[σ]∈L) := by
  classical
  simp [Shared.Supervisor.enabled,history]

private theorem history_complete {α : Type} (G : Shared.Generator α) (Ec : Set α) (L K : Set (List α)) :
    Shared.Complete G (history Ec L K) := by
  intro s σ hs hg hen
  obtain ⟨⟨x,q⟩,hx⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨q',hq'⟩ := Option.isSome_iff_exists.mp hg
  have hc := cl_components G (history Ec L K) s x q hx
  have he : x=s := Option.some.inj (hc.1.symm.trans (history_run Ec L K s))
  subst x
  have hstep : G.δ σ q=some q' := by rw [run_snoc,hc.2] at hq'; exact hq'
  apply Option.isSome_iff_exists.mpr
  refine ⟨(s++[σ],q'),?_⟩
  rw [cl_snoc,hx]
  exact (cl_step_iff G (history Ec L K) σ s (s++[σ]) q q').mpr ⟨hen s (history_run Ec L K s),rfl,hstep⟩

private theorem history_generated {α : Type} (G : Shared.Generator α) (Ec : Set α) (L K : Set (List α))
    (hLne : L.Nonempty) (hLcl : Shared.pre L=L) (hL : Controllable G Ec L) :
    Shared.Lsup G (history Ec L K)=L := by
  have hnil : ([] : List α)∈L := by
    obtain ⟨s,hs⟩ := hLne
    rw [← hLcl]
    exact ⟨s,hs⟩
  ext s
  induction s using List.reverseRecOn with
  | nil => exact ⟨fun _ => hnil,fun _ => rfl⟩
  | append_singleton s σ ih =>
    constructor
    · intro hs
      obtain ⟨⟨x',q'⟩,hx'⟩ := Option.isSome_iff_exists.mp hs
      rw [cl_snoc] at hx'
      obtain ⟨⟨x,q⟩,hx,hstep⟩ := Option.bind_eq_some_iff.mp hx'
      have hc := cl_components G (history Ec L K) s x q hx
      have he : x=s := Option.some.inj (hc.1.symm.trans (history_run Ec L K s))
      subst x
      have hen := ((cl_step_iff G (history Ec L K) σ s x' q q').mp hstep).1
      by_cases hσ : σ∈Ec
      · exact (history_enabled Ec L K s σ).mp hen hσ
      · have hpre : s∈L := ih.mp (Option.isSome_iff_exists.mpr ⟨(s,q),hx⟩)
        have hplant : s++[σ]∈G.L := by
          apply Option.isSome_iff_exists.mpr
          refine ⟨q',?_⟩
          rw [run_snoc,hc.2]
          exact ((cl_step_iff G (history Ec L K) σ s x' q q').mp hstep).2.2
        rw [← hLcl] at hpre ⊢
        exact hL.2 s σ hpre hσ hplant
    · intro hs
      have hpre : s∈L := by rw [← hLcl]; exact ⟨[σ],hs⟩
      apply history_complete G Ec L K s σ (ih.mpr hpre) (hL.1 hs)
      intro x hx
      have he : x=s := Option.some.inj (hx.symm.trans (history_run Ec L K s))
      subst x
      exact (history_enabled Ec L K s σ).mpr (fun _ => hs)

private theorem history_marked {α : Type} (G : Shared.Generator α) (Ec : Set α) (L K : Set (List α)) :
    Shared.Lmsup G (history Ec L K)=Shared.Lsup G (history Ec L K) ∩ G.Lm ∩ K := by
  ext s
  constructor
  · rintro ⟨x,q,hx,hmark,hq⟩
    have hc := cl_components G (history Ec L K) s x q hx
    have he : x=s := Option.some.inj (hc.1.symm.trans (history_run Ec L K s))
    subst x
    exact ⟨⟨Option.isSome_iff_exists.mpr ⟨(s,q),hx⟩,q,hc.2,hq⟩,hmark⟩
  · rintro ⟨⟨hs,q,hq,hqm⟩,hk⟩
    obtain ⟨⟨x,r⟩,hx⟩ := Option.isSome_iff_exists.mp hs
    have hc := cl_components G (history Ec L K) s x r hx
    have he : x=s := Option.some.inj (hc.1.symm.trans (history_run Ec L K s))
    have hr : r=q := Option.some.inj (hc.2.symm.trans hq)
    subst x; subst r
    exact ⟨s,q,hx,hk,hqm⟩

private theorem generated_controllable {α : Type} (G : Shared.Generator α) (Ec : Set α)
    (S : Shared.Supervisor α Ec) (hS : Shared.Complete G S) : Controllable G Ec (Shared.Lsup G S) := by
  constructor
  · intro s hs
    obtain ⟨⟨x,q⟩,hx⟩ := Option.isSome_iff_exists.mp hs
    exact Option.isSome_iff_exists.mpr ⟨q,(cl_components G S s x q hx).2⟩
  · intro s σ hs hσ hg
    rw [pre_generated] at hs ⊢
    apply hS s σ hs hg
    intro x hx hc
    exact False.elim (hσ hc)

private theorem marked_subset {α : Type} (G : Shared.Generator α) {Ec : Set α} (S : Shared.Supervisor α Ec) :
    Shared.Lmsup G S⊆Shared.Lcsup G S := by
  rintro s ⟨x,q,hx,hxm,hqm⟩
  exact ⟨Option.isSome_iff_exists.mpr ⟨(x,q),hx⟩,q,(cl_components G S s x q hx).2,hqm⟩

private theorem pre_mono' {α : Type} {K L : Set (List α)} (h : K⊆L) : Shared.pre K⊆Shared.pre L := by
  rintro s ⟨t,ht⟩
  exact ⟨t,h ht⟩

private theorem pre_idem {α : Type} (K : Set (List α)) : Shared.pre (Shared.pre K)=Shared.pre K := by
  ext s
  constructor
  · rintro ⟨t,u,hu⟩
    exact ⟨t++u,by simpa only [List.append_assoc] using hu⟩
  · intro hs; exact ⟨[],by simpa using hs⟩

private theorem subset_pre {α : Type} (K : Set (List α)) : K⊆Shared.pre K := fun s hs => ⟨[],by simpa using hs⟩

private theorem plant_pre {α : Type} (G : Shared.Generator α) : Shared.pre G.L=G.L := by
  ext s
  constructor
  · rintro ⟨t,ht⟩
    obtain ⟨q,hq⟩ := Option.isSome_iff_exists.mp ht
    rw [run_append] at hq
    obtain ⟨r,hr,_⟩ := Option.bind_eq_some_iff.mp hq
    exact Option.isSome_iff_exists.mpr ⟨r,hr⟩
  · exact fun hs => subset_pre G.L hs

private theorem plant_marked_sub {α : Type} (G : Shared.Generator α) : G.Lm⊆G.L := by
  rintro s ⟨q,hq,_⟩
  exact Option.isSome_iff_exists.mpr ⟨q,hq⟩

private theorem realize {α : Type} (G : Shared.Generator α) (Ec : Set α) (L K : Set (List α))
    (hLne : L.Nonempty) (hLcl : Shared.pre L=L) (hL : Controllable G Ec L) (hK : K⊆L∩G.Lm) :
    ∃ S : Shared.Supervisor α Ec, S.S.Accessible ∧ Shared.Complete G S ∧ Shared.Lsup G S=L ∧ Shared.Lmsup G S=K := by
  refine ⟨history Ec L K,history_accessible Ec L K,history_complete G Ec L K,history_generated G Ec L K hLne hLcl hL,?_⟩
  rw [history_marked,history_generated G Ec L K hLne hLcl hL]
  exact Set.inter_eq_right.mpr hK

private theorem pre_controllable {α : Type} (G : Shared.Generator α) (Ec : Set α) (K : Set (List α))
    (hK : Controllable G Ec K) : Controllable G Ec (Shared.pre K) := by
  constructor
  · have h := pre_mono' hK.1
    rwa [plant_pre] at h
  · intro s σ hs hσ hg
    rw [pre_idem] at hs ⊢
    exact hK.2 s σ hs hσ hg

private theorem proper_realize {α : Type} (G : Shared.Generator α) (Ec : Set α) (K : Set (List α))
    (hKne : K.Nonempty) (hKG : K⊆G.Lm) (hK : Controllable G Ec K) :
    ∃ S : Shared.Supervisor α Ec, S.S.Accessible ∧ Shared.Proper G S ∧ Shared.Lmsup G S=K := by
  have hKsub : K⊆Shared.pre K∩G.Lm := fun s hs => ⟨subset_pre K hs,hKG hs⟩
  obtain ⟨S,hacc,hcomp,hgen,hmark⟩ := realize G Ec (Shared.pre K) K
    (hKne.mono (subset_pre K)) (pre_idem K) (pre_controllable G Ec K hK) hKsub
  have hctrl : Shared.Lcsup G S=Shared.pre K∩G.Lm := by unfold Shared.Lcsup; rw [hgen]
  have hprectrl : Shared.pre (Shared.Lcsup G S)=Shared.pre K := by
    rw [hctrl]
    apply Set.Subset.antisymm
    · have h := pre_mono' (Set.inter_subset_left : Shared.pre K∩G.Lm⊆Shared.pre K)
      rwa [pre_idem] at h
    · exact pre_mono' hKsub
  refine ⟨S,hacc,⟨hcomp,?_,?_⟩,hmark⟩
  · exact hprectrl.trans hgen.symm
  · change Shared.pre (Shared.Lcsup G S)=Shared.pre (Shared.Lmsup G S)
    rw [hprectrl,hmark]

private theorem proper_pre_marked {α : Type} (G : Shared.Generator α) {Ec : Set α}
    (S : Shared.Supervisor α Ec) (hS : Shared.Proper G S) : Shared.pre (Shared.Lmsup G S)=Shared.Lsup G S :=
  hS.2.2.symm.trans hS.2.1

private theorem proper_marked_controllable {α : Type} (G : Shared.Generator α) (Ec : Set α)
    (S : Shared.Supervisor α Ec) (hS : Shared.Proper G S) : Controllable G Ec (Shared.Lmsup G S) := by
  constructor
  · exact (marked_subset G S).trans (fun s hs => (plant_marked_sub G) hs.2)
  · intro s σ hs hσ hg
    rw [proper_pre_marked G S hS] at hs ⊢
    apply hS.1 s σ hs hg
    intro x hx hc
    exact False.elim (hσ hc)

private theorem proper_controlled_controllable {α : Type} (G : Shared.Generator α) (Ec : Set α)
    (S : Shared.Supervisor α Ec) (hS : Shared.Proper G S) : Controllable G Ec (Shared.Lcsup G S) := by
  constructor
  · exact fun s hs => (plant_marked_sub G) hs.2
  · intro s σ hs hσ hg
    rw [hS.2.1] at hs ⊢
    apply hS.1 s σ hs hg
    intro x hx hc
    exact False.elim (hσ hc)

theorem solution {α : Type} [Fintype α] (G : Shared.Generator α) (Ec : Set α)
    (hG : G.L = Shared.pre G.Lm) (L : Set (List α)) (hLcl : Shared.IsClosedLang L) (hLG : L ⊆ G.L)
    (hS : ∃ 𝒮 : Shared.Supervisor α Ec, 𝒮.S.Accessible ∧ Shared.Complete G 𝒮 ∧ Shared.Lsup G 𝒮 = L)
    (K : Set (List α)) (hK : K ⊆ L ∩ G.Lm) :
    ∃ 𝒮K : Shared.Supervisor α Ec, 𝒮K.S.Accessible ∧ Shared.Complete G 𝒮K ∧
      Shared.Lsup G 𝒮K = L ∧ Shared.Lmsup G 𝒮K = K := by
  obtain ⟨S,hacc,hcomp,hgen⟩ := hS
  have hc := generated_controllable G Ec S hcomp
  rw [hgen] at hc
  have hne : L.Nonempty := by
    rw [← hgen]
    exact ⟨[],rfl⟩
  exact realize G Ec L K hne hLcl.symm hc hK
