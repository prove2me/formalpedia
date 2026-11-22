-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.productive_tree_eq_iff_observations
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T18:16:01.855266+00:00
-- url     : https://prove2.me/submissions/d9559c7b-b10a-479e-9559-47f2ac397523

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Semantics

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

theorem obs_iff_value {G : HORS} (t : Tm) (w : List ℕ) (c : ℕ) :
    G.Obs t w c ↔ G.BTat t w = .term c := by
  induction w generalizing t with
  | nil =>
    simp only [HORS.Obs, ← head_eq_some_iff, HORS.BTat]
    cases G.head t with
    | none => simp
    | some p => rcases p with ⟨_, _⟩; simp
  | cons i w ih =>
    simp only [HORS.Obs, ← head_eq_some_iff, HORS.BTat]
    cases G.head t with
    | none => simp
    | some p =>
      rcases p with ⟨a, us⟩
      by_cases h : i < us.length <;> simp [h, ih]

private theorem tree_at_eq {G H : HORS} (hG : G.Valid) (hH : H.Valid) (alpha : G.alphabet = H.alphabet)
    (w : List ℕ) (t u : Tm) (ht : G.typeOf [] t = some .o) (hu : H.typeOf [] u = some .o)
    (pt : G.ProdDepth t (w.length + 1)) (pu : H.ProdDepth u (w.length + 1))
    (agree : ∀ v a b, a < G.alphabet.length → b < H.alphabet.length →
      G.Obs t v a → H.Obs u v b → a = b) : G.BTat t w = H.BTat u w := by
  induction w generalizing t u with
  | nil =>
    obtain ⟨a, xs, hx, _⟩ := pt
    obtain ⟨b, ys, hy, _⟩ := pu
    have lt_of_get {l : List ℕ} {c n : ℕ} (h : l[c]? = some n) : c < l.length := by
      simpa using Option.isSome_iff_exists.mpr ⟨_, h⟩
    have hab := agree [] a b (lt_of_get (headConv_typed hG ht hx).1)
      (lt_of_get (headConv_typed hH hu hy).1) ⟨_, hx⟩ ⟨_, hy⟩
    simp [HORS.BTat, head_eq_some_iff.mpr hx, head_eq_some_iff.mpr hy, hab]
  | cons i w ih =>
    obtain ⟨a, xs, hx, px⟩ := pt
    obtain ⟨b, ys, hy, py⟩ := pu
    obtain ⟨ax, tx⟩ := headConv_typed hG ht hx
    obtain ⟨ay, ty⟩ := headConv_typed hH hu hy
    have hab := agree [] a b (by simpa using Option.isSome_iff_exists.mpr ⟨_, ax⟩)
      (by simpa using Option.isSome_iff_exists.mpr ⟨_, ay⟩) ⟨_, hx⟩ ⟨_, hy⟩
    subst b
    rw [alpha, ay] at ax
    have len := Option.some.inj ax
    rw [HORS.BTat, HORS.BTat, head_eq_some_iff.mpr hx, head_eq_some_iff.mpr hy]
    by_cases hix : i < xs.length
    · have hiy : i < ys.length := by omega
      simp only [dif_pos hix, dif_pos hiy]
      apply ih _ _ (tx _ (List.getElem_mem _)) (ty _ (List.getElem_mem _))
        (px _ (List.getElem_mem _)) (py _ (List.getElem_mem _))
      intro v a' b' h₁ h₂ o₁ o₂
      exact agree (i :: v) a' b' h₁ h₂ ⟨_, _, hx, hix, o₁⟩ ⟨_, _, hy, hiy, o₂⟩
    · have hiy : ¬ i < ys.length := by omega
      simp [hix, hiy]


private theorem proved_here {G H : HORS} (hG : G.Valid) (hH : H.Valid)
    (alpha : G.alphabet = H.alphabet) (pg : G.Prod) (ph : H.Prod) :
    G.BT = H.BT ↔ ∀ w a b, a < G.alphabet.length → b < H.alphabet.length →
      G.Obs (.nt G.start) w a → H.Obs (.nt H.start) w b → a = b := by
  constructor
  · intro eq w a b _ _ ha hb
    exact Lab.term.inj ((obs_iff_value _ _ _ |>.mp ha).symm.trans
      ((congrFun eq w).trans (obs_iff_value _ _ _ |>.mp hb)))
  · intro ha
    have start_ty (K : HORS) (hK : K.Valid) : K.typeOf [] (.nt K.start) = some .o := by
      simp only [HORS.Valid, HORS.valid, Bool.and_eq_true, beq_iff_eq] at hK
      exact hK.1.2
    funext w
    exact tree_at_eq hG hH alpha w _ _ (start_ty _ hG) (start_ty _ hH) (pg _) (ph _) ha

end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution {G H : HORS} (hG : G.Valid) (hH : H.Valid)
    (alpha : G.alphabet = H.alphabet) (pg : G.Prod) (ph : H.Prod) :
    G.BT = H.BT ↔ ∀ w a b, a < G.alphabet.length → b < H.alphabet.length →
      G.Obs (.nt G.start) w a → H.Obs (.nt H.start) w b → a = b := proved_here hG hH alpha pg ph
