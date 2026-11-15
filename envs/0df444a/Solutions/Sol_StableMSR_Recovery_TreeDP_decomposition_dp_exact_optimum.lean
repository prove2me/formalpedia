-- Prove2me | solution 1 for StableMSR.Recovery.TreeDP.decomposition_dp_exact_optimum
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-14T09:11:02.096678+00:00
-- url     : https://prove2.me/submissions/0bcfd7d8-3cea-437d-8b87-ba5c45a29d57

import Definitions.Def_StableMSR_BinaryTreeDP_Recurrence
import Theorems.Thm_StableMSR_Recovery_TreeDP_binary_plan_from_decomposition
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.RingNF
open scoped Classical BigOperators
namespace StableMSR.Recovery.TreeDP
theorem glue_two_scopes {V X : Type*} [DecidableEq V]
    (bag L R : Finset V) (parent left right : V → X)
    (hoverlap : L ∩ R ⊆ bag)
    (hleft : AgreeOn (bag ∩ L) parent left)
    (hright : AgreeOn (bag ∩ R) parent right) :
    ∃ whole : V → X, AgreeOn bag whole parent ∧
      AgreeOn L whole left ∧ AgreeOn R whole right := by
  let whole : V → X := fun v => if v ∈ L then left v else if v ∈ R then right v else parent v
  refine ⟨whole,?_,?_,?_⟩
  · intro v hv
    dsimp [whole]
    split_ifs with hL hR
    · exact (hleft v (Finset.mem_inter.mpr ⟨hv,hL⟩)).symm
    · exact (hright v (Finset.mem_inter.mpr ⟨hv,hR⟩)).symm
    · rfl
  · intro v hv
    simp only [whole,if_pos hv]
  · intro v hv
    dsimp [whole]
    split_ifs with hL
    · have hbag := hoverlap (Finset.mem_inter.mpr ⟨hL,hv⟩)
      exact (hleft v (Finset.mem_inter.mpr ⟨hbag,hL⟩)).symm.trans
        (hright v (Finset.mem_inter.mpr ⟨hbag,hv⟩))
    · rfl

theorem minimize_subset {V X : Type*} (A : Finset (Entry V X)) : minimize A ⊆ A :=
  Finset.filter_subset _ _

theorem minimize_preserves {V X : Type*} {A : Finset (Entry V X)} {a : Entry V X}
    (ha : a ∈ A) : ∃ b ∈ minimize A,
      b.1 = a.1 ∧ b.2.1 = a.2.1 ∧ b.2.2 ≤ a.2.2 := by
  classical
  let F := A.filter (fun b => b.1 = a.1 ∧ b.2.1 = a.2.1)
  have haF : a ∈ F := Finset.mem_filter.mpr ⟨ha,rfl,rfl⟩
  obtain ⟨b,hb,hmin⟩ := Finset.exists_min_image F (fun e => e.2.2) ⟨a,haF⟩
  obtain ⟨hbA,hba,hbc⟩ := Finset.mem_filter.mp hb
  refine ⟨b,Finset.mem_filter.mpr ⟨hbA,?_⟩,hba,hbc,hmin a haF⟩
  intro c hc hca hcc
  exact hmin c (Finset.mem_filter.mpr ⟨hc,hca.trans hba,hcc.trans hbc⟩)

inductive Evaluates {V X : Type*} [DecidableEq V] : Plan V X → (V → X) → ℕ → ℝ → Prop
  | leaf (d : BagData V X) (a : V → X) (ha : a ∈ d.choices) (hv : d.valid a) :
      Evaluates (.leaf d) a (d.count a) (d.weight a)
  | branch (d : BagData V X) (L R : Plan V X)
      (a al ar : V → X) (jl jr : ℕ) (wl wr : ℝ)
      (ha : a ∈ d.choices) (hv : d.valid a)
      (hl : Evaluates L al jl wl) (hr : Evaluates R ar jr wr)
      (hcl : AgreeOn (d.bag ∩ L.root.bag) a al)
      (hcr : AgreeOn (d.bag ∩ R.root.bag) a ar) :
      Evaluates (.branch d L R) a (d.count a + jl + jr) (d.weight a + wl + wr)

theorem mem_joinEntries {V X : Type*} [DecidableEq V]
    {d : BagData V X} {BL BR : Finset V} {L R : Finset (Entry V X)} {e : Entry V X} :
    e ∈ joinEntries d BL BR L R ↔
      ∃ a ∈ d.choices, d.valid a ∧ ∃ l ∈ L, ∃ r ∈ R,
        AgreeOn (d.bag ∩ BL) a l.1 ∧ AgreeOn (d.bag ∩ BR) a r.1 ∧
        e = (a,(d.count a + l.2.1 + r.2.1,d.weight a + l.2.2 + r.2.2)) := by
  classical
  simp only [joinEntries, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
    accepted]
  constructor
  · rintro ⟨⟨⟨a,l⟩,r⟩,⟨⟨⟨⟨ha,hv⟩,hl⟩,hr⟩,hcl,hcr⟩,he⟩
    exact ⟨a,ha,hv,l,hl,r,hr,hcl,hcr,he.symm⟩
  · rintro ⟨a,ha,hv,l,hl,r,hr,hcl,hcr,he⟩
    exact ⟨((a,l),r),⟨⟨⟨⟨ha,hv⟩,hl⟩,hr⟩,hcl,hcr⟩,he.symm⟩

theorem solve_sound {V X : Type*} [DecidableEq V] (cap : ℕ) (p : Plan V X)
    {e : Entry V X} (he : e ∈ solve cap p) : Evaluates p e.1 e.2.1 e.2.2 := by
  classical
  induction p generalizing e with
  | leaf d =>
    have hraw := (Finset.mem_filter.mp (minimize_subset _ he)).1
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hraw
    obtain ⟨ha,hv⟩ := Finset.mem_filter.mp ha
    exact Evaluates.leaf d a ha hv
  | branch d L R ihL ihR =>
    have hraw := (Finset.mem_filter.mp (minimize_subset _ he)).1
    obtain ⟨a,ha,hv,l,hl,r,hr,hcl,hcr,rfl⟩ := mem_joinEntries.mp hraw
    exact Evaluates.branch d L R a l.1 r.1 l.2.1 r.2.1 l.2.2 r.2.2
      ha hv (ihL hl) (ihR hr) hcl hcr

theorem solve_complete {V X : Type*} [DecidableEq V] (cap : ℕ)
    {p : Plan V X} {a : V → X} {j : ℕ} {w : ℝ}
    (heval : Evaluates p a j w) (hj : j ≤ cap) :
    ∃ e ∈ solve cap p, e.1 = a ∧ e.2.1 = j ∧ e.2.2 ≤ w := by
  classical
  induction heval with
  | leaf d a ha hv =>
    apply minimize_preserves (a := (a,(d.count a,d.weight a)))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hv⟩,rfl⟩,hj⟩
  | branch d L R a al ar jl jr wl wr ha hv hl hr hcl hcr ihL ihR =>
    obtain ⟨l,hlm,hla,hlj,hlw⟩ := ihL (by omega)
    obtain ⟨r,hrm,hra,hrj,hrw⟩ := ihR (by omega)
    let raw : Entry V X := (a,(d.count a + l.2.1 + r.2.1,d.weight a+l.2.2+r.2.2))
    have hraw : raw ∈ trim cap (joinEntries d L.root.bag R.root.bag (solve cap L) (solve cap R)) := by
      apply Finset.mem_filter.mpr
      refine ⟨mem_joinEntries.mpr ⟨a,ha,hv,l,hlm,r,hrm,?_,?_,rfl⟩,?_⟩
      · simpa only [hla] using hcl
      · simpa only [hra] using hcr
      · dsimp [raw]; simpa only [hlj,hrj] using hj
    obtain ⟨e,hem,hea,hej,hew⟩ := minimize_preserves hraw
    refine ⟨e,hem,hea,?_,?_⟩
    · dsimp [raw] at hej; simpa only [hlj,hrj] using hej
    · dsimp [raw] at hew; linarith

theorem solve_count_bound {V X : Type*} [DecidableEq V] (cap : ℕ) (p : Plan V X)
    {e : Entry V X} (he : e ∈ solve cap p) : e.2.1 ≤ cap := by
  cases p with
  | leaf d => exact (Finset.mem_filter.mp (minimize_subset _ he)).2
  | branch d L R => exact (Finset.mem_filter.mp (minimize_subset _ he)).2

theorem evaluates_root_mem {V X : Type*} [DecidableEq V]
    {p : Plan V X} {a : V → X} {j : ℕ} {w : ℝ} (h : Evaluates p a j w) :
    a ∈ p.root.choices := by
  cases h with
  | leaf d a ha hv => exact ha
  | branch d L R a al ar jl jr wl wr ha hv hl hr hcl hcr => exact ha

theorem minimize_key_injective {V X : Type*} (A : Finset (Entry V X)) :
    Set.InjOn (fun e : Entry V X => (e.1,e.2.1)) (minimize A : Set (Entry V X)) := by
  intro a ha b hb hkey
  obtain ⟨haA,hma⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbA,hmb⟩ := Finset.mem_filter.mp hb
  have hroot : a.1 = b.1 := congrArg (fun k : (V → X) × ℕ => k.1) hkey
  have hcount : a.2.1 = b.2.1 := congrArg (fun k : (V → X) × ℕ => k.2) hkey
  apply Prod.ext hroot
  apply Prod.ext hcount
  exact le_antisymm (hma b hbA hroot.symm hcount.symm) (hmb a haA hroot hcount)

/-- Number of table entries: one cost for each permitted bag assignment and count. -/
theorem solve_card_bound {V X : Type*} [DecidableEq V] (cap : ℕ) (p : Plan V X) :
    (solve cap p).card ≤ p.root.choices.card * (cap + 1) := by
  classical
  let key : Entry V X → (V → X) × ℕ := fun e => (e.1,e.2.1)
  have hinj : Set.InjOn key (solve cap p : Set (Entry V X)) := by
    cases p with
    | leaf d => exact minimize_key_injective _
    | branch d L R => exact minimize_key_injective _
  have hsub : (solve cap p).image key ⊆ p.root.choices ×ˢ Finset.range (cap+1) := by
    intro k hk
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_product.mpr ⟨evaluates_root_mem (solve_sound cap p he),
      Finset.mem_range.mpr (by change e.2.1 < cap+1; have h := solve_count_bound cap p he; omega)⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj,Finset.card_product,Finset.card_range] at hcard
  exact hcard

theorem joinEntries_card_le {V X : Type*} [DecidableEq V]
    (d : BagData V X) (BL BR : Finset V) (L R : Finset (Entry V X)) :
    (joinEntries d BL BR L R).card ≤ d.choices.card * L.card * R.card := by
  classical
  calc
    (joinEntries d BL BR L R).card ≤ (((accepted d ×ˢ L) ×ˢ R).filter _).card :=
      Finset.card_image_le
    _ ≤ ((accepted d ×ˢ L) ×ˢ R).card := Finset.card_filter_le _ _
    _ = (accepted d).card * L.card * R.card := by simp only [Finset.card_product]
    _ ≤ d.choices.card * L.card * R.card :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Finset.card_filter_le _ _))

/-- A binary bag join examines at most B^3(cap+1)^2 triples when every bag has
at most B assignments. This bounds the enumerated candidates independently of
the sizes of the child subtrees. -/
theorem solve_join_card_bound {V X : Type*} [DecidableEq V]
    (cap B : ℕ) (d : BagData V X) (L R : Plan V X)
    (hd : d.choices.card ≤ B) (hL : L.root.choices.card ≤ B) (hR : R.root.choices.card ≤ B) :
    (joinEntries d L.root.bag R.root.bag (solve cap L) (solve cap R)).card ≤
      B ^ 3 * (cap+1) ^ 2 := by
  have hl := (solve_card_bound cap L).trans (Nat.mul_le_mul_right (cap+1) hL)
  have hr := (solve_card_bound cap R).trans (Nat.mul_le_mul_right (cap+1) hR)
  calc
    (joinEntries d L.root.bag R.root.bag (solve cap L) (solve cap R)).card ≤
        d.choices.card * (solve cap L).card * (solve cap R).card := joinEntries_card_le _ _ _ _ _
    _ ≤ B * (B * (cap+1)) * (B * (cap+1)) := Nat.mul_le_mul (Nat.mul_le_mul hd hl) hr
    _ = B ^ 3 * (cap+1) ^ 2 := by ring

theorem globalEvaluates_transport {V X : Type*} [DecidableEq V]
    {p : Plan V X} {a b : V → X} {j : ℕ} {w : ℝ}
    (h : GlobalEvaluates p a j w) (hag : AgreeOn p.scope b a) : GlobalEvaluates p b j w := by
  induction h with
  | leaf d whole loc ha hv hlocal =>
    exact GlobalEvaluates.leaf d b loc ha hv (fun v hv => (hag v hv).trans (hlocal v hv))
  | branch d L R whole loc jl jr wl wr ha hv hlocal hl hr ihL ihR =>
    refine GlobalEvaluates.branch d L R b loc jl jr wl wr ha hv ?_ ?_ ?_
    · intro v hv
      exact (hag v (Finset.mem_union_left _ (Finset.mem_union_left _ hv))).trans (hlocal v hv)
    · exact ihL (fun v hv => hag v (Finset.mem_union_left _ (Finset.mem_union_right _ hv)))
    · exact ihR (fun v hv => hag v (Finset.mem_union_right _ hv))

/-- Running intersection upgrades local separator agreement into one assignment on
the whole subtree, without changing any constraint, count, or cost. -/
theorem evaluates_glue {V X : Type*} [DecidableEq V]
    {p : Plan V X} {a : V → X} {j : ℕ} {w : ℝ}
    (h : Evaluates p a j w) (hcoh : p.Coherent) :
    ∃ whole : V → X, GlobalEvaluates p whole j w ∧ AgreeOn p.root.bag whole a := by
  induction h with
  | leaf d a ha hv =>
    exact ⟨a,GlobalEvaluates.leaf d a a ha hv (fun _ _ => rfl),fun _ _ => rfl⟩
  | branch d L R a al ar jl jr wl wr ha hv hl hr hcl hcr ihL ihR =>
    rcases hcoh with ⟨hcohL,hcohR,hboundaryL,hboundaryR,hoverlap⟩
    obtain ⟨gl,hgl,hglroot⟩ := ihL hcohL
    obtain ⟨gr,hgr,hgrroot⟩ := ihR hcohR
    have hparentL : AgreeOn (d.bag ∩ L.scope) a gl := by
      intro v hv
      obtain ⟨hvb,hvs⟩ := Finset.mem_inter.mp hv
      have hvr := hboundaryL (Finset.mem_inter.mpr ⟨hvs,hvb⟩)
      exact (hcl v (Finset.mem_inter.mpr ⟨hvb,hvr⟩)).trans (hglroot v hvr).symm
    have hparentR : AgreeOn (d.bag ∩ R.scope) a gr := by
      intro v hv
      obtain ⟨hvb,hvs⟩ := Finset.mem_inter.mp hv
      have hvr := hboundaryR (Finset.mem_inter.mpr ⟨hvs,hvb⟩)
      exact (hcr v (Finset.mem_inter.mpr ⟨hvb,hvr⟩)).trans (hgrroot v hvr).symm
    obtain ⟨whole,hbag,hleft,hright⟩ :=
      glue_two_scopes d.bag L.scope R.scope a gl gr hoverlap hparentL hparentR
    exact ⟨whole,GlobalEvaluates.branch d L R whole a jl jr wl wr ha hv hbag
      (globalEvaluates_transport hgl hleft) (globalEvaluates_transport hgr hright),hbag⟩

theorem globalEvaluates_to_evaluates {V X : Type*} [DecidableEq V]
    {p : Plan V X} {whole : V → X} {j : ℕ} {w : ℝ}
    (h : GlobalEvaluates p whole j w) :
    ∃ a, Evaluates p a j w ∧ AgreeOn p.root.bag whole a := by
  induction h with
  | leaf d whole a ha hv hag => exact ⟨a,Evaluates.leaf d a ha hv,hag⟩
  | branch d L R whole a jl jr wl wr ha hv hag hl hr ihL ihR =>
    obtain ⟨al,hel,hal⟩ := ihL
    obtain ⟨ar,her,har⟩ := ihR
    refine ⟨a,Evaluates.branch d L R a al ar jl jr wl wr ha hv hel her ?_ ?_,hag⟩
    · intro v hv
      exact (hag v (Finset.mem_inter.mp hv).1).symm.trans (hal v (Finset.mem_inter.mp hv).2)
    · intro v hv
      exact (hag v (Finset.mem_inter.mp hv).1).symm.trans (har v (Finset.mem_inter.mp hv).2)

theorem solve_global_sound {V X : Type*} [DecidableEq V] (cap : ℕ) (p : Plan V X)
    (hcoh : p.Coherent) {e : Entry V X} (he : e ∈ solve cap p) :
    ∃ whole : V → X, GlobalEvaluates p whole e.2.1 e.2.2 ∧ AgreeOn p.root.bag whole e.1 :=
  evaluates_glue (solve_sound cap p he) hcoh

theorem solve_global_complete {V X : Type*} [DecidableEq V] (cap : ℕ)
    {p : Plan V X} {whole : V → X} {j : ℕ} {w : ℝ}
    (h : GlobalEvaluates p whole j w) (hj : j ≤ cap) :
    ∃ e ∈ solve cap p, AgreeOn p.root.bag whole e.1 ∧ e.2.1 = j ∧ e.2.2 ≤ w := by
  obtain ⟨a,he,hagree⟩ := globalEvaluates_to_evaluates h
  obtain ⟨e,hem,hea,hej,hew⟩ := solve_complete cap he hj
  exact ⟨e,hem,hea ▸ hagree,hej,hew⟩

/-- Minimizing the root table at the requested count returns a globally optimal
feasible assignment for that count. The witness comes from the finite recurrence. -/
theorem solve_root_optimum {V X : Type*} [DecidableEq V]
    (cap : ℕ) (p : Plan V X) (hcoh : p.Coherent) (j : ℕ) (hj : j ≤ cap)
    (hfeasible : ∃ whole w, GlobalEvaluates p whole j w) :
    ∃ e ∈ solve cap p, e.2.1 = j ∧
      (∃ whole, GlobalEvaluates p whole j e.2.2) ∧
      ∀ whole w, GlobalEvaluates p whole j w → e.2.2 ≤ w := by
  classical
  let F := (solve cap p).filter (fun e => e.2.1 = j)
  obtain ⟨whole,w,hglobal⟩ := hfeasible
  obtain ⟨seed,hseed,_,hcseed,_⟩ := solve_global_complete cap hglobal hj
  have hseedF : seed ∈ F := Finset.mem_filter.mpr ⟨hseed,hcseed⟩
  obtain ⟨e,he,hmin⟩ := Finset.exists_min_image F (fun e => e.2.2) ⟨seed,hseedF⟩
  obtain ⟨hem,hej⟩ := Finset.mem_filter.mp he
  obtain ⟨winner,hwinner,_⟩ := solve_global_sound cap p hcoh hem
  refine ⟨e,hem,hej,⟨winner,hej ▸ hwinner⟩,?_⟩
  intro other cost hother
  obtain ⟨entry,hentry,_,hcount,hcost⟩ := solve_global_complete cap hother hj
  exact (hmin entry (Finset.mem_filter.mpr ⟨hentry,hcount⟩)).trans hcost

theorem globalEvaluates_accounting {V X : Type*} [DecidableEq V]
    {p : Plan V X} {whole : V → X} {j : ℕ} {w : ℝ}
    (h : GlobalEvaluates p whole j w) (hloc : p.Local) :
    p.AllValid whole ∧ p.totalCount whole = j ∧ p.totalWeight whole = w := by
  induction h with
  | leaf d whole a ha hv hag =>
    obtain ⟨hvalid,hcount,hweight⟩ := hloc whole a hag
    exact ⟨hvalid.mpr hv,hcount,hweight⟩
  | branch d L R whole a jl jr wl wr ha hv hag hl hr ihL ihR =>
    obtain ⟨hvalid,hcount,hweight⟩ := hloc.1 whole a hag
    obtain ⟨hvl,hjl,hwl⟩ := ihL hloc.2.1
    obtain ⟨hvr,hjr,hwr⟩ := ihR hloc.2.2
    refine ⟨⟨hvalid.mpr hv,hvl,hvr⟩,?_,?_⟩
    · change d.count whole + L.totalCount whole + R.totalCount whole = _
      rw [hcount,hjl,hjr]
    · change d.weight whole + L.totalWeight whole + R.totalWeight whole = _
      rw [hweight,hwl,hwr]

theorem globalEvaluates_choice_cover {V X : Type*} [DecidableEq V]
    {p : Plan V X} {whole : V → X} {j : ℕ} {w : ℝ}
    (h : GlobalEvaluates p whole j w) :
    p.AllData (fun d => ∃ a ∈ d.choices, AgreeOn d.bag whole a) := by
  induction h with
  | leaf d whole a ha hv hag => exact ⟨a,ha,hag⟩
  | branch d L R whole a jl jr wl wr ha hv hag hl hr ihL ihR =>
    exact ⟨⟨a,ha,hag⟩,ihL,ihR⟩

theorem globalEvaluates_of_choice_cover {V X : Type*} [DecidableEq V]
    (p : Plan V X) (whole : V → X) (hloc : p.Local) (hv : p.AllValid whole)
    (hc : p.AllData (fun d => ∃ a ∈ d.choices, AgreeOn d.bag whole a)) :
    GlobalEvaluates p whole (p.totalCount whole) (p.totalWeight whole) := by
  induction p with
  | leaf d =>
    obtain ⟨a,ha,hag⟩ := hc
    obtain ⟨hvalid,hcount,hweight⟩ := hloc whole a hag
    simpa only [Plan.totalCount,Plan.totalWeight,←hcount,←hweight] using
      GlobalEvaluates.leaf d whole a ha (hvalid.mp hv) hag
  | branch d L R ihL ihR =>
    obtain ⟨⟨a,ha,hag⟩,hcL,hcR⟩ := hc
    obtain ⟨hvalid,hcount,hweight⟩ := hloc.1 whole a hag
    simpa only [Plan.totalCount,Plan.totalWeight,←hcount,←hweight] using
      GlobalEvaluates.branch d L R whole a (L.totalCount whole) (R.totalCount whole)
        (L.totalWeight whole) (R.totalWeight whole) ha (hvalid.mp hv.1) hag
        (ihL hloc.2.1 hv.2.1 hcL) (ihR hloc.2.2 hv.2.2 hcR)

theorem globalEvaluates_iff_choices {V X : Type*} [DecidableEq V]
    (p : Plan V X) (hloc : p.Local) (whole : V → X) (j : ℕ) (w : ℝ) :
    GlobalEvaluates p whole j w ↔
      p.AllValid whole ∧
      p.AllData (fun d => ∃ a ∈ d.choices, AgreeOn d.bag whole a) ∧
      p.totalCount whole = j ∧ p.totalWeight whole = w := by
  constructor
  · intro h
    obtain ⟨hv,hj,hw⟩ := globalEvaluates_accounting h hloc
    exact ⟨hv,globalEvaluates_choice_cover h,hj,hw⟩
  · rintro ⟨hv,hc,rfl,rfl⟩
    exact globalEvaluates_of_choice_cover p whole hloc hv hc



/-- Sum of all retained table sizes, including leaves. This is a size bound,
not a bound on instruction execution. -/
lemma allData_mono {V X : Type*} {P Q : BagData V X → Prop} {p : Plan V X}
    (hp : p.AllData P) (hpq : ∀ d, P d → Q d) : p.AllData Q := by
  induction p with
  | leaf d => exact hpq d hp
  | branch d L R ihL ihR => exact ⟨hpq d hp.1,ihL hp.2.1,ihR hp.2.2⟩

lemma allData_root {V X : Type*} {P : BagData V X → Prop} {p : Plan V X}
    (h : p.AllData P) : P p.root := by
  cases p with
  | leaf d => exact h
  | branch d L R => exact h.1

theorem tableVolume_le {V X : Type*} [DecidableEq V] (p : Plan V X) (cap B : ℕ)
    (h : p.AllData (fun d => d.choices.card ≤ B)) :
    p.tableVolume cap ≤ p.nodes * (B * (cap+1)) := by
  have hb : ∀ q : Plan V X, q.AllData (fun d => d.choices.card ≤ B) →
      (solve cap q).card ≤ B * (cap+1) := by
    intro q hq
    exact (solve_card_bound cap q).trans (Nat.mul_le_mul_right _ (allData_root hq))
  induction p with
  | leaf d => simpa [Plan.tableVolume,Plan.nodes] using hb (.leaf d) h
  | branch d L R ihL ihR =>
    have ht := hb (.branch d L R) h
    have hl := ihL h.2.1
    have hr := ihR h.2.2
    simp only [Plan.tableVolume,Plan.nodes]
    nlinarith

/-- Number of leaf choices and raw parent/left/right triples before filtering.
This deliberately includes invalid or inconsistent candidates. -/
theorem rawCandidateVolume_le {V X : Type*} [DecidableEq V]
    (p : Plan V X) (cap B : ℕ) (h : p.AllData (fun d => d.choices.card ≤ B)) :
    p.rawCandidateVolume cap ≤ p.nodes * (B ^ 3 * (cap+1) ^ 2) := by
  have hpow : B ≤ B ^ 3 := Nat.le_self_pow (by decide) B
  have hleaf : B ≤ B ^ 3 * (cap+1) ^ 2 := by
    exact hpow.trans (Nat.le_mul_of_pos_right _ (pow_pos (Nat.succ_pos cap) _))
  induction p with
  | leaf d => simpa [Plan.rawCandidateVolume,Plan.nodes] using h.trans hleaf
  | branch d L R ihL ihR =>
    have hl := (solve_card_bound cap L).trans (Nat.mul_le_mul_right _ (allData_root h.2.1))
    have hr := (solve_card_bound cap R).trans (Nat.mul_le_mul_right _ (allData_root h.2.2))
    have ht : d.choices.card * (solve cap L).card * (solve cap R).card ≤ B ^ 3 * (cap+1) ^ 2 := by
      calc
        _ ≤ B * (B * (cap+1)) * (B * (cap+1)) := Nat.mul_le_mul (Nat.mul_le_mul h.1 hl) hr
        _ = _ := by ring
    have hL := ihL h.2.1
    have hR := ihR h.2.2
    simp only [Plan.rawCandidateVolume,Plan.nodes]
    nlinarith

end StableMSR.Recovery.TreeDP
open StableMSR.Recovery.TreeDP
/-- The finite DP on a genuine tree decomposition realizes precisely the original
locally representable assignments, with the original total count and objective. -/
theorem solution {V X T : Type} [DecidableEq V]
    [Fintype T] [DecidableEq T] (G : SimpleGraph V) (tree : SimpleGraph T)
    (data : T → BagData V X)
    (htd : RobertsonSeymour1986.GM5.IsTreeDecomposition G tree (fun t => (data t).bag))
    (root : T) (width choices : ℕ)
    (hlocal : ∀ t, (data t).Local)
    (hbound : ∀ t, (data t).bag.card ≤ width ∧ (data t).choices.card ≤ choices) :
    ∃ p : Plan V X,
      p.Coherent ∧ p.Local ∧ p.nodes + 1 = 2 * Fintype.card T ∧
      p.AllData (fun d => d.bag.card ≤ width ∧ d.choices.card ≤ choices) ∧
      (∀ cap, (solve cap p).card ≤ choices * (cap + 1)) ∧
      (∀ cap,
        p.tableVolume cap ≤ (2 * Fintype.card T - 1) * (choices * (cap+1)) ∧
        p.rawCandidateVolume cap ≤ (2 * Fintype.card T - 1) * (choices ^ 3 * (cap+1) ^ 2)) ∧
      (∀ (whole : V → X) (j : ℕ) (w : ℝ),
        GlobalEvaluates p whole j w ↔
          (∀ t, (data t).valid whole) ∧
          (∀ t, ∃ a ∈ (data t).choices, AgreeOn (data t).bag whole a) ∧
          (∑ t, (data t).count whole) = j ∧ (∑ t, (data t).weight whole) = w) ∧
      ∀ cap j, j ≤ cap →
        (∃ whole : V → X, (∀ t, (data t).valid whole) ∧
          (∀ t, ∃ a ∈ (data t).choices, AgreeOn (data t).bag whole a) ∧
          (∑ t, (data t).count whole) = j) →
        ∃ e ∈ solve cap p, ∃ whole : V → X,
          e.2.1 = j ∧ (∀ t, (data t).valid whole) ∧
          (∀ t, ∃ a ∈ (data t).choices, AgreeOn (data t).bag whole a) ∧
          (∑ t, (data t).count whole) = j ∧
          (∑ t, (data t).weight whole) = e.2.2 ∧
          ∀ other : V → X, (∀ t, (data t).valid other) →
            (∀ t, ∃ a ∈ (data t).choices, AgreeOn (data t).bag other a) →
            (∑ t, (data t).count other) = j → e.2.2 ≤ ∑ t, (data t).weight other := by
  obtain ⟨p,hcoh,hloc,hbag,hchoices,hscope,hacc,hnodes,hbounds⟩ :=
    binary_plan_from_decomposition G tree data htd root width choices hlocal hbound
  have hsem (whole : V → X) (j : ℕ) (w : ℝ) :
      GlobalEvaluates p whole j w ↔
        (∀ t, (data t).valid whole) ∧
        (∀ t, ∃ a ∈ (data t).choices, AgreeOn (data t).bag whole a) ∧
        (∑ t, (data t).count whole) = j ∧ (∑ t, (data t).weight whole) = w := by
    rw [globalEvaluates_iff_choices p hloc]
    obtain ⟨hv,hc,hj,hw⟩ := hacc whole
    rw [hv,hc,hj,hw]
  have hallchoices : p.AllData (fun d => d.choices.card ≤ choices) :=
    allData_mono hbounds (fun _ h => h.2)
  have hnodes' : p.nodes = 2 * Fintype.card T - 1 := by omega
  refine ⟨p,hcoh,hloc,hnodes,hbounds,?_,?_,hsem,?_⟩
  · intro cap
    calc
      (solve cap p).card ≤ p.root.choices.card * (cap + 1) := solve_card_bound cap p
      _ = (data root).choices.card * (cap + 1) := by rw [hchoices]
      _ ≤ choices * (cap + 1) := Nat.mul_le_mul_right _ (hbound root).2
  · intro cap
    constructor
    · simpa only [hnodes'] using tableVolume_le p cap choices hallchoices
    · simpa only [hnodes'] using rawCandidateVolume_le p cap choices hallchoices
  · intro cap j hj hfeasible
    obtain ⟨seed,hvalid,hcover,hcount⟩ := hfeasible
    have hseed : GlobalEvaluates p seed j (∑ t, (data t).weight seed) :=
      (hsem seed j _).mpr ⟨hvalid,hcover,hcount,rfl⟩
    obtain ⟨e,he,hej,⟨winner,hwinner⟩,hmin⟩ :=
      solve_root_optimum cap p hcoh j hj ⟨seed,_,hseed⟩
    obtain ⟨hv,hc,hj',hw⟩ := (hsem winner j e.2.2).mp hwinner
    refine ⟨e,he,winner,hej,hv,hc,hj',hw,?_⟩
    intro other hvother hcother hjother
    exact hmin other _ ((hsem other j _).mpr ⟨hvother,hcother,hjother,rfl⟩)

