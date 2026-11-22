-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.binary_translation_correct
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T18:28:44.52546+00:00
-- url     : https://prove2.me/submissions/75db24cd-17c8-48ed-b4f2-14658b730d8c

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Encoding
import Definitions.Def_TreeEquivalenceHORS_Equivalence_BinaryOutput

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

private theorem nta (G : HORS) (i : ℕ) : (binaryScheme G).nts[3+i]? = G.nts[i]? := by
  change (sigma0.map termTy ++ G.nts)[3+i]? = _
  rw [List.getElem?_append_right (by simp [sigma0] : (sigma0.map termTy).length ≤ 3+i)]
  simp [sigma0]

private theorem rulea (G : HORS) (i : ℕ) : (binaryScheme G).rules[3+i]? = G.rules[i]?.map binaryTerm := by
  change (binaryRules ++ G.rules.map binaryTerm)[3+i]? = _
  rw [List.getElem?_append_right (by simp [binaryRules] : binaryRules.length ≤ 3+i)]
  simp [binaryRules]

private theorem binary_type (G : HORS) (ag : G.alphabet = sigma0) (ctx : List Ty) (t : Tm) :
    (binaryScheme G).typeOf ctx (binaryTerm t) = G.typeOf ctx t := by
  induction t with
  | var i => rfl
  | nt i => exact nta _ _
  | tm i =>
    by_cases h : i < 3
    · obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      all_goals simp [binaryTerm, HORS.typeOf, binaryScheme, ag, sigma0]
    · simp [binaryTerm, h, HORS.typeOf, binaryScheme, ag, sigma0, sigma2]
  | app t u it iu => simp only [binaryTerm, HORS.typeOf, it, iu]

private theorem binary_vars (t : Tm) : (binaryTerm t).vars = t.vars := by
  induction t with
  | tm i => by_cases h : i < 3 <;> simp [binaryTerm, h, Tm.vars]
  | app t u ht hu => simp [binaryTerm, Tm.vars, *]
  | _ => rfl

private theorem binary_safeTm (G : HORS) (ag : G.alphabet = sigma0) (ctx : List Ty) (t : Tm) :
    (binaryScheme G).safeTm ctx (binaryTerm t) = G.safeTm ctx t := by
  induction t with
  | var i => rfl
  | nt i => simp only [binaryTerm, HORS.safeTm, HORS.typeOf, nta]
  | tm i =>
    have eq := binary_type G ag ctx (.tm i)
    by_cases h : i < 3 <;> simp only [binaryTerm, if_pos, if_neg, h, not_false_eq_true] at eq ⊢ <;>
      simp only [HORS.safeTm, eq]
  | app t u ht hu =>
    unfold HORS.safeTm
    simp only [binaryTerm, ht, hu, binary_vars, binary_type G ag]
    rw [← binaryTerm.eq_4, binary_type G ag]

private theorem binary_order (G : HORS) : (binaryScheme G).order ≤ max 1 G.order := by
  change (sigma0.map termTy ++ G.nts |>.map Ty.ord |>.foldr max 0) ≤ _
  simp [sigma0, termTy, Ty.ofArgs, Ty.ord, HORS.order]

private theorem shifted_rule (G : HORS) (ag : G.alphabet = sigma0) (i : ℕ) :
    (binaryScheme G).ruleOK (3+i) = G.ruleOK i ∧ (binaryScheme G).ruleSafe (3+i) = G.ruleSafe i := by
  simp only [HORS.ruleOK, HORS.ruleSafe, nta, rulea]
  cases G.nts[i]? <;> cases G.rules[i]? <;> simp [binary_type G ag, binary_safeTm G ag]

private theorem fresh_rules (G : HORS) (i : ℕ) (hi : i < 3) :
    (binaryScheme G).ruleOK i = true ∧ (binaryScheme G).ruleSafe i = true := by
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  all_goals exact ⟨rfl, rfl⟩

theorem binary_static (G : HORS) (vg : G.Valid) (ag : G.alphabet = sigma0) :
    (binaryScheme G).Valid ∧ (binaryScheme G).alphabet = sigma2 ∧
    (binaryScheme G).order ≤ max 1 G.order ∧ (G.Safe → (binaryScheme G).Safe) := by
  have len : (binaryScheme G).nts.length = 3 + G.nts.length := by simp [binaryScheme, sigma0]; omega
  have lengthRules : (binaryScheme G).rules.length = 3 + G.rules.length := by simp [binaryScheme, binaryRules]; omega
  simp only [HORS.Valid, HORS.valid, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at vg ⊢
  refine ⟨⟨⟨by rw [lengthRules, len, vg.1.1], (nta _ _).trans vg.1.2⟩, ?_⟩, rfl, binary_order G, ?_⟩
  · intro i hi
    by_cases hf : i < 3
    · exact (fresh_rules G i hf).1
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hf)
      rw [(shifted_rule G ag j).1]
      exact vg.2 _ (by omega)
  · simp only [HORS.Safe, List.all_eq_true, List.mem_range]
    intro hs i hi
    by_cases hf : i < 3
    · exact (fresh_rules G i hf).2
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hf)
      rw [(shifted_rule G ag j).2]
      exact hs _ (by omega)

private theorem binary_spine (t : Tm) :
    (binaryTerm t).spine = (binaryTerm t.spine.1, t.spine.2.map binaryTerm) := by
  induction t with
  | var i | nt i => rfl
  | tm i => by_cases h : i < 3 <;> simp [binaryTerm, Tm.spine, h]
  | app t u ih _ => simp [binaryTerm, Tm.spine, ih]

private theorem binary_subst (t : Tm) (args : List Tm) :
    (binaryTerm t).subst (args.map binaryTerm) = binaryTerm (t.subst args) := by
  induction t with
  | var i =>
    simp only [binaryTerm, Tm.subst, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases args[i]? <;> rfl
  | nt i => rfl
  | tm i => by_cases h : i < 3 <;> simp [binaryTerm, Tm.subst, h]
  | app t u it iu => simp [binaryTerm, Tm.subst, it, iu]

private theorem binary_step (G : HORS) {t u : Tm} (hs : G.HeadStep t u) :
    (binaryScheme G).HeadStep (binaryTerm t) (binaryTerm u) := by
  unfold HORS.HeadStep HORS.headStep at *
  rw [binary_spine]
  split at hs <;> try contradiction
  rename_i F args sp
  simp only [sp, binaryTerm, nta, rulea, List.length_map]
  cases hn : G.nts[F]? <;> cases hr : G.rules[F]? <;> simp [hn, hr] at hs ⊢
  exact ⟨hs.1, (binary_subst _ _).trans (congrArg binaryTerm hs.2)⟩

private inductive SourceHead where
  | z
  | a (x : Tm)
  | b (x y z : Tm)

private def SourceHead.source : SourceHead → ℕ × List Tm
  | .z => (0, [])
  | .a x => (1, [x])
  | .b x y u => (2, [x,y,u])

private def SourceHead.target : SourceHead → ℕ × List Tm
  | .z => (0, [])
  | .a x => (1, [binaryLeaf, binaryTerm x])
  | .b x y u => (1, [binaryFork binaryLeaf binaryLeaf, binaryFork (binaryTerm x) (binaryFork (binaryTerm y) (binaryTerm u))])

private theorem of_arity {c : ℕ} {xs : List Tm} (h : sigma0[c]? = some xs.length) :
    ∃ s : SourceHead, s.source = (c, xs) := by
  have hc : c < 3 := by simpa [sigma0] using Option.isSome_iff_exists.mpr ⟨_, h⟩
  obtain rfl | rfl | rfl : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  · simp [sigma0] at h
    have hx := List.length_eq_zero_iff.mp h.symm
    subst xs
    exact ⟨.z, rfl⟩
  · cases xs with
    | nil => simp [sigma0] at h
    | cons x xs => cases xs <;> simp [sigma0] at h; exact ⟨.a x,rfl⟩
  · cases xs with
    | nil => simp [sigma0] at h
    | cons x xs =>
      cases xs with
      | nil => simp [sigma0] at h
      | cons y xs =>
        cases xs with
        | nil => simp [sigma0] at h
        | cons z xs => cases xs <;> simp [sigma0] at h; exact ⟨.b x y z,rfl⟩

private theorem translated_head (G : HORS) (s : SourceHead) {t : Tm}
    (h : G.HeadConv t s.source.1 s.source.2) :
    (binaryScheme G).head (binaryTerm t) = some s.target := by
  obtain ⟨u, steps, sp⟩ := h
  have reach : Relation.ReflTransGen (binaryScheme G).HeadStep (binaryTerm t) (binaryTerm u) :=
    steps.lift binaryTerm (fun _ _ h => binary_step G h)
  have extra (v : Tm) (hs : (binaryScheme G).HeadStep (binaryTerm u) v)
      (hv : v.spine = (.tm s.target.1, s.target.2)) : (binaryScheme G).head (binaryTerm t) = some s.target :=
    head_eq_some_iff.mpr ⟨_, reach.tail hs, hv⟩
  cases s with
  | z =>
    apply extra binaryLeaf _ rfl
    simp [HORS.HeadStep, HORS.headStep, binary_spine, sp, SourceHead.source, binaryTerm]
    rfl
  | a x =>
    apply extra (binaryFork binaryLeaf (binaryTerm x)) _ rfl
    simp [HORS.HeadStep, HORS.headStep, binary_spine, sp, SourceHead.source, binaryTerm]
    rfl
  | b x y z =>
    apply extra (binaryFork (binaryFork binaryLeaf binaryLeaf) (binaryFork (binaryTerm x) (binaryFork (binaryTerm y) (binaryTerm z)))) _ rfl
    simp [HORS.HeadStep, HORS.headStep, binary_spine, sp, SourceHead.source, binaryTerm]
    rfl

private theorem head_children {G : HORS} {t : Tm} {c : ℕ} {xs : List Tm}
    (h : G.HeadConv t c xs) (hp : ∀ d, G.ProdDepth t d) (x : Tm) (hx : x ∈ xs) :
    ∀ d, G.ProdDepth x d := by
  intro d
  obtain ⟨b, ys, hh, hy⟩ := hp (d+1)
  obtain he := headConv_unique h hh
  cases he
  exact hy x hx

private theorem head_leaf (G : HORS) : G.head binaryLeaf = some (0,[]) :=
  head_eq_some_iff.mpr ⟨binaryLeaf, .refl, rfl⟩

private theorem head_fork (G : HORS) (x y : Tm) : G.head (binaryFork x y) = some (1,[x,y]) :=
  head_eq_some_iff.mpr ⟨_, .refl, rfl⟩

private theorem at_leaf (G : HORS) (w : List ℕ) : G.BTat binaryLeaf w = if w = [] then .term 0 else .absent := by
  cases w <;> simp [HORS.BTat, head_leaf]

private theorem at_fork (G : HORS) (x y : Tm) (i : ℕ) (w : List ℕ) :
    G.BTat (binaryFork x y) (i :: w) = if i=0 then G.BTat x w else if i=1 then G.BTat y w else .absent := by
  rcases i with _ | ⟨_|i⟩ <;> simp [HORS.BTat, head_fork]

private theorem binary_at (G : HORS) (vg : G.Valid) (ag : G.alphabet = sigma0)
    (w : List ℕ) (t : Tm) (ht : G.typeOf [] t = some .o) (hp : ∀ d, G.ProdDepth t d) :
    (binaryScheme G).BTat (binaryTerm t) w = encAt (G.BTat t) w := by
  obtain ⟨c, xs, h, _⟩ := hp 1
  obtain ⟨hcs, hts⟩ := headConv_typed vg ht h
  obtain ⟨s, hs⟩ := of_arity (ag ▸ hcs)
  have h' : G.HeadConv t s.source.1 s.source.2 := by simpa [hs] using h
  have ho := head_eq_some_iff.mpr h'
  have hk := translated_head G s h'
  have typed : ∀ u ∈ s.source.2, G.typeOf [] u = some .o := by simpa [hs] using hts
  have prod := head_children h' hp
  have sub (i : ℕ) (v : List ℕ) (hi : i < s.source.2.length) (hv : v.length < w.length) :
      (binaryScheme G).BTat (binaryTerm s.source.2[i]) v =
        encAt (fun y => G.BTat t (i :: y)) v := by
    have ht' := typed s.source.2[i] (List.getElem_mem _)
    have hp' := prod s.source.2[i] (List.getElem_mem _)
    simpa only [HORS.BTat, ho, dif_pos hi] using binary_at G vg ag v _ ht' hp'
  rw [encAt.eq_def]
  cases s with
  | z =>
    cases w <;> simp [HORS.BTat, hk, ho, SourceHead.source, SourceHead.target]
  | a x =>
    cases w with
    | nil => simp [HORS.BTat, hk, ho, SourceHead.source, SourceHead.target]
    | cons i w =>
      rcases i with _ | ⟨_|i⟩
      · simp [HORS.BTat, hk, ho, SourceHead.source, SourceHead.target, at_leaf]
      · have he := sub 0 w (by simp [SourceHead.source]) (by simp only [List.length_cons]; omega)
        simpa [HORS.BTat, hk, ho, SourceHead.source, SourceHead.target] using he
      · simp [HORS.BTat, hk, ho, SourceHead.source, SourceHead.target]
  | b x y z =>
    cases w with
    | nil => simp [HORS.BTat, hk, ho, SourceHead.source, SourceHead.target]
    | cons i w =>
      rcases i with _ | ⟨_|i⟩
      · cases w with
        | nil => simp [HORS.BTat, hk, ho, SourceHead.source, SourceHead.target, head_fork]
        | cons j w =>
          rcases j with _ | ⟨_|j⟩ <;> cases w <;>
            simp [HORS.BTat, hk, ho, SourceHead.source, SourceHead.target, head_fork, head_leaf]
      · cases w with
        | nil => simp [HORS.BTat, hk, ho, SourceHead.source, SourceHead.target, head_fork]
        | cons j w =>
          rcases j with _ | ⟨_|j⟩
          · have he := sub 0 w (by simp [SourceHead.source]) (by simp only [List.length_cons]; omega)
            simpa [HORS.BTat, hk, ho, SourceHead.source, SourceHead.target, head_fork] using he
          · cases w with
            | nil => simp [HORS.BTat, hk, ho, SourceHead.source, SourceHead.target, head_fork]
            | cons k w =>
              rcases k with _ | ⟨_|k⟩
              · have he := sub 1 w (by simp [SourceHead.source]) (by simp only [List.length_cons]; omega)
                simpa [HORS.BTat, hk, ho, SourceHead.source, SourceHead.target, head_fork] using he
              · have he := sub 2 w (by simp [SourceHead.source]) (by simp only [List.length_cons]; omega)
                simpa [HORS.BTat, hk, ho, SourceHead.source, SourceHead.target, head_fork] using he
              · simp [HORS.BTat, hk, ho, SourceHead.source, SourceHead.target, head_fork]
          · simp [HORS.BTat, hk, ho, SourceHead.source, SourceHead.target, head_fork]
      · simp [HORS.BTat, hk, ho, SourceHead.source, SourceHead.target]
termination_by w.length

private theorem depth_down {G : HORS} (d : ℕ) (t : Tm) (h : G.ProdDepth t (d+1)) : G.ProdDepth t d := by
  induction d generalizing t with
  | zero => trivial
  | succ d ih =>
    obtain ⟨c, xs, h, hc⟩ := h
    exact ⟨c, xs, h, fun x hx => ih x (hc x hx)⟩

private theorem leaf_prod (G : HORS) (d : ℕ) : G.ProdDepth binaryLeaf d := by
  cases d with
  | zero => trivial
  | succ d => exact ⟨0, [], head_eq_some_iff.mp (head_leaf G), by simp⟩

private theorem fork_prod (G : HORS) (d : ℕ) (x y : Tm) (hx : G.ProdDepth x d) (hy : G.ProdDepth y d) :
    G.ProdDepth (binaryFork x y) d := by
  cases d with
  | zero => trivial
  | succ d =>
    refine ⟨1,[x,y], head_eq_some_iff.mp (head_fork G x y), ?_⟩
    simpa using And.intro (depth_down d x hx) (depth_down d y hy)

private theorem binary_depth (G : HORS) (vg : G.Valid) (ag : G.alphabet = sigma0)
    (d : ℕ) (t : Tm) (ht : G.typeOf [] t = some .o) (hp : ∀ n, G.ProdDepth t n) :
    (binaryScheme G).ProdDepth (binaryTerm t) d := by
  induction d generalizing t with
  | zero => trivial
  | succ d ih =>
    obtain ⟨c, xs, h, _⟩ := hp 1
    obtain ⟨hcs, hts⟩ := headConv_typed vg ht h
    obtain ⟨s, hs⟩ := of_arity (ag ▸ hcs)
    have h' : G.HeadConv t s.source.1 s.source.2 := by simpa [hs] using h
    refine ⟨s.target.1, s.target.2, head_eq_some_iff.mp (translated_head G s h'), ?_⟩
    have child (x : Tm) (hx : x ∈ s.source.2) : (binaryScheme G).ProdDepth (binaryTerm x) d :=
      ih x (hts x (by simpa [hs] using hx)) (head_children h' hp _ hx)
    cases s with
    | z => simp [SourceHead.target]
    | a x => simpa [SourceHead.target] using And.intro (leaf_prod _ d) (child x (by simp [SourceHead.source]))
    | b x y z =>
      simpa [SourceHead.target] using And.intro (fork_prod _ d _ _ (leaf_prod _ d) (leaf_prod _ d))
        (fork_prod _ d _ _ (child x (by simp [SourceHead.source]))
          (fork_prod _ d _ _ (child y (by simp [SourceHead.source])) (child z (by simp [SourceHead.source]))))


private theorem proved_here (G : HORS) (vg : G.Valid) (ag : G.alphabet = sigma0) (pg : G.Prod) :
    (binaryScheme G).Valid ∧ (binaryScheme G).alphabet = sigma2 ∧ (binaryScheme G).Prod ∧
    (binaryScheme G).order ≤ max 1 G.order ∧ (binaryScheme G).BT = encAt G.BT ∧ (G.Safe → (binaryScheme G).Safe) := by
  obtain ⟨v,a,o,s⟩ := binary_static G vg ag
  have ty : G.typeOf [] (.nt G.start) = some .o := by
    simp only [HORS.Valid, HORS.valid, Bool.and_eq_true, beq_iff_eq] at vg
    exact vg.1.2
  exact ⟨v,a,fun d => binary_depth G vg ag d _ ty pg, o, funext (fun w => binary_at G vg ag w _ ty pg), s⟩

end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution (G : HORS) (vg : G.Valid) (ag : G.alphabet = sigma0) (pg : G.Prod) :
    (binaryScheme G).Valid ∧ (binaryScheme G).alphabet = sigma2 ∧ (binaryScheme G).Prod ∧
    (binaryScheme G).order ≤ max 1 G.order ∧ (binaryScheme G).BT = encAt G.BT ∧ (G.Safe → (binaryScheme G).Safe) := proved_here G vg ag pg
