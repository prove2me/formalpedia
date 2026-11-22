-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.lemma_5_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T17:56:57.341916+00:00
-- url     : https://prove2.me/submissions/f837b040-d2fd-46b7-b0ef-ce77836ccb47

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Compiler
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_1
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_5
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_6

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
private theorem headConv_step {G : HORS} {t u : Tm} (step : G.HeadStep t u) (a : ℕ) (us : List Tm) :
    G.HeadConv t a us ↔ G.HeadConv u a us := by
  constructor
  · rintro ⟨s, hs, spine⟩
    rcases hs.cases_head with rfl | ⟨s', h', htail⟩
    · simp [HORS.HeadStep, HORS.headStep, spine] at step
    · have eq : u = s' := Option.some.inj (step.symm.trans h')
      exact ⟨s, eq ▸ htail, spine⟩
  · rintro ⟨s, hs, spine⟩
    exact ⟨s, hs.head step, spine⟩

theorem obs_step {G : HORS} {t u : Tm} (hs : G.HeadStep t u) (w : List ℕ) (c : ℕ) :
    G.Obs t w c ↔ G.Obs u w c := by
  cases w <;> simp only [HORS.Obs, headConv_step hs]

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

/-- At each reachable address the map exposes a label and has a full subtree at every ranked child. -/
private def Full : ℕ → Val .o → Prop
  | 0, _ => True
  | d + 1, T => ∃ a : Fin 3, T [] = some a ∧
      ∀ i < sigma0.getD a.val 0, Full d (fun w => T (i :: w))

private theorem obs_after_steps {G : HORS} {t u : Tm} (hs : Relation.ReflTransGen G.HeadStep t u)
    (w : List ℕ) (a : ℕ) : G.Obs t w a ↔ G.Obs u w a := by
  induction hs with
  | refl => rfl
  | tail _ h ih => exact ih.trans (obs_step h w a)

private theorem prod_of_full {G : HORS} (hG : G.Valid) (hAlphabet : G.alphabet = sigma0)
    (d : ℕ) (t : Tm) (ht : G.typeOf [] t = some .o) (T : Val .o)
    (hr : Real G .o t T) (hf : Full d T) : G.ProdDepth t d := by
  induction d generalizing t T with
  | zero => trivial
  | succ d ih =>
    obtain ⟨a, ha, hc⟩ := hf
    obtain ⟨us, hu⟩ := (hr [] a).mpr ha
    obtain ⟨arity, typed⟩ := headConv_typed hG ht hu
    have len : sigma0.getD a.val 0 = us.length := by
      simp [List.getD_eq_getElem?_getD, ← hAlphabet, arity]
    obtain ⟨v, steps, spine⟩ := hu
    refine ⟨a.val, us, ⟨v, steps, spine⟩, ?_⟩
    intro u hm
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
    refine ih _ (typed _ (List.getElem_mem ..)) _ ?_ (hc i (len ▸ hi))
    intro w b
    have hh := (obs_after_steps steps (i :: w) b).symm.trans (hr (i :: w) b)
    simpa [HORS.Obs, terminal_conv (G := G) spine, hi] using hh

private theorem full_z (d : ℕ) : Full d zVal := by
  cases d with
  | zero => trivial
  | succ d => exact ⟨0, rfl, fun i hi => nomatch (show i < 0 from hi)⟩

private theorem full_chain (n d : ℕ) : Full d (chainVal n) := by
  induction d generalizing n with
  | zero => trivial
  | succ d ih =>
    cases n with
    | zero => exact ⟨0, rfl, fun i hi => nomatch (show i < 0 from hi)⟩
    | succ n =>
      refine ⟨1, by simp [chainVal], fun i hi => ?_⟩
      have ei : i = 0 := by change i < 1 at hi; omega
      have same : (fun w => chainVal (n + 1) (i :: w)) = chainVal n := by
        funext w
        simp [ei, chainVal]
      exact same.symm ▸ ih n

private theorem full_K (d : ℕ) : Full d kVal := by
  induction d with
  | zero => trivial
  | succ d ih =>
    refine ⟨2, rfl, fun i hi => ?_⟩
    change i < 3 at hi
    interval_cases i <;> simp only [kVal] <;> first | exact ih | exact full_z d

private theorem full_state (side : Side) (M : Machine) (d m i : ℕ) (R : PairState) :
    Full d (Tmap side M m i R) := by
  induction d generalizing m i R with
  | zero => trivial
  | succ d ih =>
    refine ⟨2, rfl, fun c hc => ?_⟩
    change c < 3 at hc
    by_cases hi : M.Active i
    · interval_cases c <;> simp [Tmap, hi] <;> first | exact ih .. | exact full_z d
    · interval_cases c <;> simp [Tmap, hi] <;> first | exact full_K d | exact full_chain _ d

private theorem proved_here (M : Machine) (side : Side) : (compile side M).Prod := by
  intro d
  have hr := (lemma_5_5 side M).2 [] (by simp [Machine.IsCand])
  have start : (compile side M).HeadStep (.nt (compile side M).start)
      (callF M 1 Machine.initArgs.toList) := rfl
  apply prod_of_full (lemma_5_1 M side).1 rfl d _ rfl (Tmap side M 0 1 Machine.initPairs)
  · exact fun w a => (obs_step start w a).trans (lemma_5_6 side M 0 1 _ _ hr w a)
  · exact full_state ..

end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution (M : Machine) (side : Side) : (compile side M).Prod := proved_here M side
