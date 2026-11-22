-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.trees_equal_iff_prefixes
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T18:25:05.789241+00:00
-- url     : https://prove2.me/submissions/877c5dfc-0f3d-47fd-9e0e-db439eb9d3d5

import Definitions.Def_TreeEquivalenceHORS_Equivalence_FiniteSemantics

namespace TreeEquivalenceHORS.Equivalence

private theorem ofArgs_args (τ : Ty) : Ty.ofArgs τ.args = τ := by
  induction τ with
  | o => rfl
  | arr σ τ _ ih => simp [Ty.args, Ty.ofArgs, ih]

private theorem args_ofArgs (l : List Ty) : (Ty.ofArgs l).args = l := by
  induction l <;> simp [Ty.ofArgs, Ty.args, *]

private theorem app_typed_inv {G : HORS} {ctx : List Ty} {t u : Tm} {τ : Ty}
    (h : G.typeOf ctx (t.app u) = some τ) :
    ∃ σ, G.typeOf ctx t = some (.arr σ τ) ∧ G.typeOf ctx u = some σ := by
  unfold HORS.typeOf at h
  split at h <;> simp_all

private theorem spine_typed {G : HORS} {ctx : List Ty} (t : Tm) {τ : Ty}
    (h : G.typeOf ctx t = some τ) :
    ∃ tys, G.typeOf ctx t.spine.1 = some (Ty.ofArgs (tys ++ τ.args)) ∧
      t.spine.2.map (G.typeOf ctx) = tys.map some := by
  induction t generalizing τ with
  | var i | nt i | tm i => exact ⟨[], by simpa [ofArgs_args, Tm.spine] using h, rfl⟩
  | app t u ih _ =>
    obtain ⟨σ, ht, hu⟩ := app_typed_inv h
    obtain ⟨tys, hhead, hargs⟩ := ih ht
    exact ⟨tys ++ [σ], by simpa [Tm.spine, Ty.args] using hhead,
      by simp [Tm.spine, hargs, hu]⟩

private theorem subst_typed {G : HORS} {ctx : List Ty} {args : List Tm}
    (htys : args.map (G.typeOf []) = ctx.map some) (t : Tm) {τ : Ty}
    (h : G.typeOf ctx t = some τ) : G.typeOf [] (t.subst args) = some τ := by
  induction t generalizing τ with
  | var i =>
    have hh := congrArg (fun l : List (Option Ty) => l[i]?) htys
    change ctx[i]? = some τ at h
    simp only [List.getElem?_map, h, Option.map_some] at hh
    cases ha : args[i]? with
    | none => simp [ha] at hh
    | some u => simpa [Tm.subst, List.getD_eq_getElem?_getD, ha] using Option.some.inj (by simpa [ha] using hh : some (G.typeOf [] u) = some (some τ))
  | nt i | tm i => exact h
  | app t u ih₁ ih₂ =>
    obtain ⟨σ, ht, hu⟩ := app_typed_inv h
    simp [Tm.subst, HORS.typeOf, ih₁ ht, ih₂ hu]

theorem step_typed {G : HORS} (hG : G.Valid) {t u : Tm}
    (ht : G.typeOf [] t = some .o) (hs : G.HeadStep t u) : G.typeOf [] u = some .o := by
  obtain ⟨tys, hhead, hargs⟩ := spine_typed t ht
  unfold HORS.HeadStep HORS.headStep at hs
  split at hs <;> try contradiction
  rename_i F args sp
  simp only [sp, HORS.typeOf, Ty.args, List.append_nil] at hhead
  simp only [sp] at hargs
  rw [hhead] at hs
  cases hr : G.rules[F]? with
  | none => simp [hr] at hs
  | some body =>
    simp only [hr, args_ofArgs] at hs
    split at hs <;> try contradiction
    obtain rfl := Option.some.inj hs
    apply subst_typed hargs
    have hi : F < G.nts.length := by simpa using (Option.isSome_iff_exists.mpr ⟨_, hhead⟩)
    simp only [HORS.Valid, HORS.valid, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hG
    simpa [HORS.ruleOK, hhead, hr, args_ofArgs] using hG.2 F hi

theorem headConv_typed {G : HORS} (hG : G.Valid) {t : Tm} (ht : G.typeOf [] t = some .o)
    {c : ℕ} {us : List Tm} (hc : G.HeadConv t c us) :
    G.alphabet[c]? = some us.length ∧ ∀ u ∈ us, G.typeOf [] u = some .o := by
  obtain ⟨v, hv, hsp⟩ := hc
  have htv : G.typeOf [] v = some .o := by
    clear hsp
    induction hv with
    | refl => exact ht
    | tail _ hs ih => exact step_typed hG ih hs
  obtain ⟨tys, hh, hu⟩ := spine_typed v htv
  simp only [hsp, HORS.typeOf, Ty.args, List.append_nil] at hh
  simp only [hsp] at hu
  cases he : G.alphabet[c]? with
  | none => simp [he] at hh
  | some r =>
    simp only [he, Option.map_some, Option.some.injEq] at hh
    have ha := congrArg Ty.args hh
    simp only [termTy, args_ofArgs] at ha
    subst tys
    have len := congrArg List.length hu
    simp only [List.length_map, List.length_replicate] at len
    refine ⟨by rw [len], fun u hm => ?_⟩
    have mem : G.typeOf [] u ∈ us.map (G.typeOf []) := List.mem_map_of_mem hm
    rw [hu] at mem
    simpa using (List.eq_of_mem_replicate (by simpa only [List.map_replicate] using mem))

theorem terminal_conv {G : HORS} {t : Tm} {c : ℕ} {args : List Tm}
    (head : t.spine = (.tm c, args)) (a : ℕ) (us : List Tm) :
    G.HeadConv t a us ↔ c = a ∧ args = us := by
  constructor
  · rintro ⟨t', hs, h⟩
    rcases hs.cases_head with rfl | ⟨v, step, _⟩
    · simpa [head] using h
    · simp [HORS.HeadStep, HORS.headStep, head] at step
  · rintro ⟨rfl, rfl⟩
    exact ⟨t, .refl, head⟩


theorem exposed_eq {t : Tm} {c : ℕ} {us : List Tm} :
    exposed t = some (c, us) ↔ t.spine = (.tm c, us) := by
  unfold exposed
  rcases t.spine with ⟨h, args⟩
  cases h <;> simp

theorem run_reaches (G : HORS) (t : Tm) (n : ℕ) :
    Relation.ReflTransGen G.HeadStep t (G.run n t) := by
  induction n generalizing t with
  | zero => exact .refl
  | succ n ih =>
    cases hs : G.headStep t with
    | none => simpa [HORS.run, hs] using (Relation.ReflTransGen.refl (r := G.HeadStep) (a := t))
    | some u => simpa [HORS.run, hs] using (ih u).head (show G.HeadStep t u from hs)

private theorem budget_of_steps {G : HORS} {t u : Tm} (h : Relation.ReflTransGen G.HeadStep t u) :
    ∃ n, G.run n t = u := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n+1, by simp only [HORS.run, show G.headStep _ = some _ from hs, hn]⟩

theorem headConv_unique {G : HORS} {t : Tm} {c a : ℕ} {us vs : List Tm}
    (hc : G.HeadConv t c us) (ha : G.HeadConv t a vs) : (c, us) = (a, vs) := by
  obtain ⟨u, hu, sp⟩ := hc
  induction hu using Relation.ReflTransGen.head_induction_on with
  | refl => exact Prod.ext (terminal_conv sp a vs |>.mp ha).1 (terminal_conv sp a vs |>.mp ha).2
  | head hs _ ih =>
    apply ih
    obtain ⟨v, hv, sv⟩ := ha
    rcases hv.cases_head with rfl | ⟨w, hw, tail⟩
    · simp [HORS.HeadStep, HORS.headStep, sv] at hs
    · exact ⟨v, Option.some.inj (hs.symm.trans hw) ▸ tail, sv⟩

theorem head_eq_some_iff {G : HORS} {t : Tm} {c : ℕ} {us : List Tm} :
    G.head t = some (c, us) ↔ G.HeadConv t c us := by
  classical
  unfold HORS.head
  split
  next hex =>
    constructor
    · exact fun h => ⟨_, run_reaches G t _, exposed_eq.mp h⟩
    · intro h
      obtain ⟨⟨a, vs⟩, hv⟩ := Option.isSome_iff_exists.mp (Nat.find_spec hex)
      exact hv.trans (congrArg some (headConv_unique ⟨_, run_reaches G t _, exposed_eq.mp hv⟩ h))
  next hn =>
    simp only [reduceCtorEq, false_iff]
    rintro ⟨v, h, hv⟩
    obtain ⟨n, rfl⟩ := budget_of_steps h
    exact hn ⟨n, Option.isSome_iff_exists.mpr ⟨_, exposed_eq.mpr hv⟩⟩

private theorem mem_addrs (b d : ℕ) (w : List ℕ) :
    w ∈ addrs b d ↔ w.length < d ∧ ∀ i ∈ w, i < b := by
  induction d generalizing w with
  | zero => simp [addrs]
  | succ d ih =>
    cases w with
    | nil => simp [addrs]
    | cons i w => simp [addrs, ih, and_left_comm]

private theorem arity_le {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rcases List.mem_cons.mp hx with rfl | h
    · exact Nat.le_max_left _ _
    · exact (ih h).trans (Nat.le_max_right _ _)

private theorem outside_absent (G : HORS) (vg : G.Valid) (w : List ℕ) (t : Tm)
    (ht : G.typeOf [] t = some .o) (h : ¬∀ i ∈ w, i < G.maxArity) :
    G.BTat t w = .absent := by
  induction w generalizing t with
  | nil => simp at h
  | cons i w ih =>
    cases he : G.head t with
    | none => simp [HORS.BTat, he]
    | some p =>
      obtain ⟨c, us⟩ := p
      obtain ⟨arity, ty⟩ := headConv_typed vg ht (head_eq_some_iff.mp he)
      have le : us.length ≤ G.maxArity := arity_le (List.mem_of_getElem? arity)
      by_cases hi : i < us.length
      · simp only [HORS.BTat, he, dif_pos hi]
        apply ih _ (ty _ (List.getElem_mem _))
        intro hw
        exact h (by simpa using And.intro (hi.trans_le le) hw)
      · simp [HORS.BTat, he, hi]


private theorem proved_here (G H : HORS) (vg : G.Valid) (vh : H.Valid)
    (alph : G.alphabet = H.alphabet) (t u : Tm)
    (ht : G.typeOf [] t = some .o) (hu : H.typeOf [] u = some .o) :
    G.BTat t = H.BTat u ↔ ∀ d, G.Pref t d = H.Pref u d := by
  have ar : G.maxArity = H.maxArity := congrArg (List.foldr max 0) alph
  constructor
  · intro h d
    simp [HORS.Pref, ar, h]
  · intro pref
    funext w
    by_cases h : ∀ i ∈ w, i < G.maxArity
    · have mem := (mem_addrs G.maxArity (w.length+1) w).mpr ⟨by omega, h⟩
      have Hmem : (w, G.BTat t w) ∈ H.Pref u (w.length+1) := pref _ ▸ (List.mem_map_of_mem mem)
      obtain ⟨v, _, heq⟩ := List.mem_map.mp Hmem
      have eq : w = v ∧ G.BTat t w = H.BTat u v := by simpa using heq.symm
      exact eq.1.symm ▸ eq.2
    · rw [outside_absent G vg w t ht h, outside_absent H vh w u hu (ar ▸ h)]


end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution (G H : HORS) (vg : G.Valid) (vh : H.Valid)
    (alph : G.alphabet = H.alphabet) (t u : Tm)
    (ht : G.typeOf [] t = some .o) (hu : H.typeOf [] u = some .o) :
    G.BTat t = H.BTat u ↔ ∀ d, G.Pref t d = H.Pref u d := proved_here G H vg vh alph t u ht hu
