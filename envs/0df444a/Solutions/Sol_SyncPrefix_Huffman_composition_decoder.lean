-- Prove2me | solution 1 for SyncPrefix.Huffman.composition_decoder
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-26T22:51:54.679836+00:00
-- url     : https://prove2.me/submissions/e1acb7db-7cd7-4b81-932d-e4810910db59

import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Constructions

open SyncPrefix.Huffman Computability

section CB

set_option linter.unusedSectionVars false

variable {σ α β : Type} [DecidableEq α]

lemma cb_mem_lang (Z : Finset (List α)) (w : List α) : w ∈ lang Z ↔ w ∈ Z := Iff.rfl

lemma cb_run_cons (δ : σ → β → σ) (q : σ) (b : β) (y : List β) :
    run δ q (b :: y) = run δ (δ q b) y := rfl

lemma cb_run_append (δ : σ → β → σ) (q : σ) (u v : List β) :
    run δ q (u ++ v) = run δ (run δ q u) v := List.foldl_append

lemma cb_subst_cons (Z : Finset (List α)) (e : β ≃ {z // z ∈ Z}) (b : β) (y : List β) :
    subst (Z := lang Z) e (b :: y) = (e b).val ++ subst (Z := lang Z) e y := rfl

lemma cb_subst_nil (Z : Finset (List α)) (e : β ≃ {z // z ∈ Z}) :
    subst (Z := lang Z) e [] = [] := by
  simp [subst]

/-- A codeword is never a prefix of a vertex in `properPrefixes`. -/
lemma cb_no_code_prefix (Z : Finset (List α)) (hZ : IsPrefixCode (lang Z))
    (p : List α) (hp : p ∈ properPrefixes Z) (z : List α) (hz : z ∈ Z) (hzp : z <+: p) :
    False := by
  simp only [properPrefixes, Finset.mem_insert, Finset.mem_filter, allPrefixes,
    Finset.mem_biUnion, List.mem_toFinset, List.mem_inits] at hp
  rcases hp with rfl | ⟨⟨z', hz', hpz'⟩, hpZ⟩
  · have : z = [] := List.prefix_nil.1 hzp
    subst this
    exact hZ.1 hz
  · have h1 : z = z' := hZ.2 z hz z' hz' (hzp.trans hpz')
    subst h1
    have : p = z := hpz'.eq_of_length (le_antisymm hpz'.length_le hzp.length_le)
    exact hpZ (this ▸ hz)

lemma cb_flatten (Z : Finset (List α)) (e : β ≃ {z // z ∈ Z}) :
    ∀ L : List (List α), (∀ z ∈ L, z ∈ Z) → ∃ zs : List β, subst (Z := lang Z) e zs = L.flatten := by
  intro L
  induction L with
  | nil => intro _; exact ⟨[], cb_subst_nil Z e⟩
  | cons z L ih =>
    intro h
    obtain ⟨zs, hzs⟩ := ih (fun z' hz' => h z' (List.mem_cons_of_mem _ hz'))
    refine ⟨e.symm ⟨z, h z (List.mem_cons_self ..)⟩ :: zs, ?_⟩
    rw [cb_subst_cons, hzs]
    simp

lemma cb_subst_len (Z : Finset (List α)) (e : β ≃ {z // z ∈ Z}) (M : ℕ)
    (hM : ∀ b, (e b).val.length ≤ M) :
    ∀ y : List β, (subst (Z := lang Z) e y).length ≤ M * y.length := by
  intro y
  induction y with
  | nil => simp [subst]
  | cons b y ih =>
    rw [cb_subst_cons, List.length_append, List.length_cons]
    have := hM b
    nlinarith

/-- Parsing from a vertex `p` along a word that completes `p` into a product of codewords ends at
the root of the copy hanging from the expected state. -/
lemma cb_parse (δY : σ → β → σ) (Z : Finset (List α)) (hZ : IsPrefixCode (lang Z))
    (e : β ≃ {z // z ∈ Z}) :
    ∀ (v : List α) (p : {p // p ∈ properPrefixes Z}) (zs : List β),
      p.val ++ v = subst (Z := lang Z) e zs → ∀ q : σ,
        run (composeDecoder δY Z e) (q, p) v = rootState Z (run δY q zs) := by
  intro v
  induction v with
  | nil =>
    intro p zs hp q
    cases zs with
    | nil =>
      rw [cb_subst_nil] at hp
      simp at hp
      show (q, p) = rootState Z q
      unfold rootState
      congr 1
      exact Subtype.ext hp
    | cons b zs =>
      exfalso
      rw [cb_subst_cons, List.append_nil] at hp
      exact cb_no_code_prefix Z hZ p.val p.2 (e b).val (e b).2 ⟨_, hp.symm⟩
  | cons x v ih =>
    intro p zs hp q
    cases zs with
    | nil =>
      rw [cb_subst_nil] at hp; simp at hp
    | cons b zs =>
      rw [cb_subst_cons] at hp
      show run _ (composeDecoder δY Z e (q, p) x) v = _
      by_cases h1 : p.val ++ [x] ∈ Z
      · -- the codeword `p x` equals `e b`
        have hpre : p.val ++ [x] <+: (e b).val ++ subst (Z := lang Z) e zs :=
          ⟨v, by simp only [List.append_assoc, List.singleton_append]; exact hp⟩
        have hpre2 : (e b).val <+: (e b).val ++ subst (Z := lang Z) e zs := List.prefix_append _ _
        have heq : p.val ++ [x] = (e b).val := by
          rcases List.prefix_or_prefix_of_prefix hpre hpre2 with h | h
          · exact hZ.2 _ h1 _ (e b).2 h
          · exact (hZ.2 _ (e b).2 _ h1 h).symm
        have hstep : composeDecoder δY Z e (q, p) x =
            rootState Z (δY q (e.symm ⟨p.val ++ [x], h1⟩)) := by
          simp [composeDecoder, h1]
        have hb : e.symm ⟨p.val ++ [x], h1⟩ = b := by
          rw [Equiv.symm_apply_eq]; exact Subtype.ext heq
        rw [hstep, hb, cb_run_cons]
        apply ih
        rw [← heq] at hp
        simp at hp
        simpa using hp
      · by_cases h2 : p.val ++ [x] ∈ properPrefixes Z
        · have hstep : composeDecoder δY Z e (q, p) x = (q, ⟨p.val ++ [x], h2⟩) := by
            simp [composeDecoder, h1, h2]
          rw [hstep]
          apply ih
          rw [cb_subst_cons, ← hp]; simp
        · exfalso
          have hpre : p.val ++ [x] <+: (e b).val ++ subst (Z := lang Z) e zs :=
            ⟨v, by simp only [List.append_assoc, List.singleton_append]; exact hp⟩
          have hpre2 : (e b).val <+: (e b).val ++ subst (Z := lang Z) e zs :=
            List.prefix_append _ _
          rcases List.prefix_or_prefix_of_prefix hpre hpre2 with h | h
          · apply h2
            simp only [properPrefixes, Finset.mem_insert, Finset.mem_filter, allPrefixes,
              Finset.mem_biUnion, List.mem_toFinset, List.mem_inits]
            exact Or.inr ⟨⟨(e b).val, (e b).2, h⟩, h1⟩
          · -- `e b` is a prefix of `p x`; it is not `p x`, so it is a prefix of `p`
            have hne : (e b).val ≠ p.val ++ [x] := fun h' => h1 (h' ▸ (e b).2)
            have hlen : (e b).val.length < (p.val ++ [x]).length := by
              rcases Nat.lt_or_ge (e b).val.length (p.val ++ [x]).length with hl | hl
              · exact hl
              · exact absurd (h.eq_of_length (le_antisymm h.length_le hl)) hne
            have hpp : p.val <+: p.val ++ [x] := List.prefix_append _ _
            have : (e b).val <+: p.val :=
              List.prefix_of_prefix_length_le h hpp (by simp at hlen; omega)
            exact cb_no_code_prefix Z hZ p.val p.2 (e b).val (e b).2 this

/-- The decoder's second component evolves independently of the first; the consumed letters
cost at least `m` input letters each. -/
lemma cb_lower (δY : σ → β → σ) (Z : Finset (List α)) (e : β ≃ {z // z ∈ Z}) (m : ℕ)
    (hm : ∀ b, m ≤ (e b).val.length) :
    ∀ (w : List α) (p : {p // p ∈ properPrefixes Z}), ∃ (y : List β)
      (p' : {p // p ∈ properPrefixes Z}),
      (∀ q : σ, run (composeDecoder δY Z e) (q, p) w = (run δY q y, p')) ∧
        m * y.length + p'.val.length ≤ p.val.length + w.length := by
  intro w
  induction w with
  | nil => intro p; exact ⟨[], p, fun q => rfl, by simp⟩
  | cons x w ih =>
    intro p
    by_cases h1 : p.val ++ [x] ∈ Z
    · obtain ⟨y, p', hy, hlen⟩ := ih ⟨[], Finset.mem_insert_self _ _⟩
      refine ⟨e.symm ⟨p.val ++ [x], h1⟩ :: y, p', fun q => ?_, ?_⟩
      · show run _ (composeDecoder δY Z e (q, p) x) w = _
        have hstep : composeDecoder δY Z e (q, p) x =
            rootState Z (δY q (e.symm ⟨p.val ++ [x], h1⟩)) := by
          simp [composeDecoder, h1]
        rw [hstep]; exact hy _
      · have := hm (e.symm ⟨p.val ++ [x], h1⟩)
        simp only [Equiv.apply_symm_apply, List.length_append, List.length_singleton] at this
        simp only [List.length_cons, List.length_nil] at hlen ⊢
        nlinarith
    · by_cases h2 : p.val ++ [x] ∈ properPrefixes Z
      · obtain ⟨y, p', hy, hlen⟩ := ih ⟨p.val ++ [x], h2⟩
        refine ⟨y, p', fun q => ?_, ?_⟩
        · show run _ (composeDecoder δY Z e (q, p) x) w = _
          have hstep : composeDecoder δY Z e (q, p) x = (q, ⟨p.val ++ [x], h2⟩) := by
            simp [composeDecoder, h1, h2]
          rw [hstep]; exact hy _
        · simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
          omega
      · obtain ⟨y, p', hy, hlen⟩ := ih ⟨[], Finset.mem_insert_self _ _⟩
        refine ⟨y, p', fun q => ?_, ?_⟩
        · show run _ (composeDecoder δY Z e (q, p) x) w = _
          have hstep : composeDecoder δY Z e (q, p) x = rootState Z q := by
            simp [composeDecoder, h1, h2]
          rw [hstep]; exact hy _
        · simp only [List.length_nil, List.length_cons] at hlen ⊢
          omega



lemma cd_mem_all (Z : Finset (List α)) (u : List α) :
    u ∈ allPrefixes Z ↔ ∃ z ∈ Z, u <+: z := by
  simp [allPrefixes, List.mem_inits]

lemma cd_mem_pp (Z : Finset (List α)) (u : List α) :
    u ∈ properPrefixes Z ↔ u = [] ∨ ((∃ z ∈ Z, u <+: z) ∧ u ∉ Z) := by
  simp [properPrefixes, allPrefixes, List.mem_inits]

/-- Maximality: every child of an inner vertex is a codeword or an inner vertex. -/
lemma cd_ext (Z : Finset (List α)) (hZ : IsMaximalPrefixCode (lang Z))
    (p : List α) (hp : p ∈ properPrefixes Z) (x : α) :
    p ++ [x] ∈ Z ∨ p ++ [x] ∈ properPrefixes Z := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  set u := p ++ [x] with hu
  have hnot1 : ∀ z ∈ Z, ¬ u <+: z := by
    intro z hz huz
    exact h2 ((cd_mem_pp Z u).2 (Or.inr ⟨⟨z, hz, huz⟩, h1⟩))
  have hnot2 : ∀ z ∈ Z, ¬ z <+: u := by
    intro z hz hzu
    have hne : z ≠ u := fun h => h1 (h ▸ hz)
    have hlen : z.length < u.length := by
      rcases Nat.lt_or_ge z.length u.length with hl | hl
      · exact hl
      · exact absurd (hzu.eq_of_length (le_antisymm hzu.length_le hl)) hne
    have hpp : p <+: u := List.prefix_append _ _
    have : z <+: p := List.prefix_of_prefix_length_le hzu hpp (by simp [hu] at hlen; omega)
    exact cb_no_code_prefix Z hZ.1 p hp z hz this
  let X' : Language α := {w | w ∈ Z ∨ w = u}
  have hX' : IsPrefixCode X' := by
    refine ⟨?_, ?_⟩
    · rintro (h | h)
      · exact hZ.1.1 h
      · simp [hu] at h
    · rintro a (ha | rfl) b (hb | rfl) hab
      · exact hZ.1.2 a ha b hb hab
      · exact absurd hab (hnot2 a ha)
      · exact absurd hab (hnot1 b hb)
      · rfl
  have hle : lang Z ≤ X' := fun w hw => Or.inl hw
  have := hZ.2 X' hX' hle
  have hmem : u ∈ X' := Or.inr rfl
  rw [this] at hmem
  exact h1 hmem

lemma cd_nonempty (Z : Finset (List α)) [Nonempty α] (hZ : IsMaximalPrefixCode (lang Z)) :
    ∃ z, z ∈ Z := by
  obtain ⟨x⟩ := ‹Nonempty α›
  rcases cd_ext Z hZ [] (Finset.mem_insert_self _ _) x with h | h
  · exact ⟨_, h⟩
  · rw [cd_mem_pp] at h
    rcases h with h | ⟨⟨z, hz, _⟩, _⟩
    · simp at h
    · exact ⟨z, hz⟩

lemma cd_pp_prefix (Z : Finset (List α)) [Nonempty α] (hZ : IsMaximalPrefixCode (lang Z))
    (p : List α) (hp : p ∈ properPrefixes Z) : ∃ z ∈ Z, p <+: z := by
  rw [cd_mem_pp] at hp
  rcases hp with rfl | ⟨h, _⟩
  · obtain ⟨z, hz⟩ := cd_nonempty Z hZ
    exact ⟨z, hz, List.nil_prefix⟩
  · exact h

lemma cd_subst_append (Z : Finset (List α)) (e : β ≃ {z // z ∈ Z}) (u v : List β) :
    subst (Z := lang Z) e (u ++ v) = subst (Z := lang Z) e u ++ subst (Z := lang Z) e v := by
  simp [subst]

lemma cd_subst_ne_nil (Z : Finset (List α)) (hZ : IsPrefixCode (lang Z))
    (e : β ≃ {z // z ∈ Z}) (u : List β) (hu : u ≠ []) : subst (Z := lang Z) e u ≠ [] := by
  cases u with
  | nil => exact absurd rfl hu
  | cons b u =>
    rw [cb_subst_cons]
    intro h
    have : (e b).val = [] := (List.append_eq_nil_iff.1 h).1
    exact hZ.1 (this ▸ (e b).2)

/-- Exact parse for a maximal prefix code. -/
lemma cd_parse2 (δY : σ → β → σ) (Z : Finset (List α)) (hZ : IsMaximalPrefixCode (lang Z))
    (e : β ≃ {z // z ∈ Z}) :
    ∀ (w : List α) (p : {p // p ∈ properPrefixes Z}), ∃ (y : List β)
      (p' : {p // p ∈ properPrefixes Z}),
      (∀ q : σ, run (composeDecoder δY Z e) (q, p) w = (run δY q y, p')) ∧
        p.val ++ w = subst (Z := lang Z) e y ++ p'.val := by
  intro w
  induction w with
  | nil => intro p; exact ⟨[], p, fun q => rfl, by simp [cb_subst_nil]⟩
  | cons x w ih =>
    intro p
    rcases cd_ext Z hZ p.val p.2 x with h1 | h2
    · obtain ⟨y, p', hy, hw⟩ := ih ⟨[], Finset.mem_insert_self _ _⟩
      refine ⟨e.symm ⟨p.val ++ [x], h1⟩ :: y, p', fun q => ?_, ?_⟩
      · show run _ (composeDecoder δY Z e (q, p) x) w = _
        have hstep : composeDecoder δY Z e (q, p) x =
            rootState Z (δY q (e.symm ⟨p.val ++ [x], h1⟩)) := by
          simp [composeDecoder, h1]
        rw [hstep]; exact hy _
      · rw [cb_subst_cons, Equiv.apply_symm_apply]
        simp only [List.nil_append] at hw
        simp [hw]
    · have h1 : p.val ++ [x] ∉ Z := by
        intro h
        rw [cd_mem_pp] at h2
        rcases h2 with h2 | ⟨_, h2⟩
        · simp at h2
        · exact h2 h
      obtain ⟨y, p', hy, hw⟩ := ih ⟨p.val ++ [x], h2⟩
      refine ⟨y, p', fun q => ?_, ?_⟩
      · show run _ (composeDecoder δY Z e (q, p) x) w = _
        have hstep : composeDecoder δY Z e (q, p) x = (q, ⟨p.val ++ [x], h2⟩) := by
          simp [composeDecoder, h1, h2]
        rw [hstep]; exact hy _
      · simp only [List.append_assoc, List.singleton_append] at hw
        exact hw

/-- Reading a vertex from the root walks down the tree. -/
lemma cd_read (δY : σ → β → σ) (Z : Finset (List α)) (hZ : IsPrefixCode (lang Z))
    (e : β ≃ {z // z ∈ Z}) (q : σ) :
    ∀ (u : List α) (p : {p // p ∈ properPrefixes Z}) (h : p.val ++ u ∈ properPrefixes Z),
      run (composeDecoder δY Z e) (q, p) u = (q, ⟨p.val ++ u, h⟩) := by
  intro u
  induction u with
  | nil => intro p h; simp only [List.append_nil]; rfl
  | cons x u ih =>
    intro p h
    show run _ (composeDecoder δY Z e (q, p) x) u = _
    have hpre : p.val ++ [x] <+: p.val ++ x :: u := by
      refine ⟨u, by simp⟩
    have h1 : p.val ++ [x] ∉ Z := fun hz =>
      cb_no_code_prefix Z hZ _ h _ hz hpre
    have h2 : p.val ++ [x] ∈ properPrefixes Z := by
      rw [cd_mem_pp] at h ⊢
      rcases h with h | ⟨⟨z, hz, hz'⟩, _⟩
      · simp at h
      · exact Or.inr ⟨⟨z, hz, hpre.trans hz'⟩, h1⟩
    have hstep : composeDecoder δY Z e (q, p) x = (q, ⟨p.val ++ [x], h2⟩) := by
      simp [composeDecoder, h1, h2]
    rw [hstep, ih ⟨p.val ++ [x], h2⟩ (by simpa using h)]
    congr 2
    simp

end CB

theorem solution {σ α β : Type} [Fintype σ] [DecidableEq σ] [Fintype α] [Nonempty α]
    [DecidableEq α] (δY : σ → β → σ) (Z : Finset (List α))
    (hZ : IsMaximalPrefixCode (lang Z)) (e : β ≃ {z // z ∈ Z}) :
    Fintype.card α * Fintype.card (DecoderState σ Z) + Fintype.card σ =
        Fintype.card σ * (allPrefixes Z).card ∧
      (StronglyConnected δY → StronglyConnected (composeDecoder δY Z e)) ∧
      (IsHuffmanDecoder δY → IsHuffmanDecoder (composeDecoder δY Z e)) ∧
      ∀ (r : σ) (w : List α), run (composeDecoder δY Z e) (rootState Z r) w = rootState Z r ↔
        ∃ y : List β, run δY r y = r ∧ w = subst e y := by
  have hPC := hZ.1
  -- (c)
  have hc : ∀ (r : σ) (w : List α),
      run (composeDecoder δY Z e) (rootState Z r) w = rootState Z r ↔
        ∃ y : List β, run δY r y = r ∧ w = subst (Z := lang Z) e y := by
    intro r w
    constructor
    · intro h
      obtain ⟨y, p', hy, hw⟩ := cd_parse2 δY Z hZ e w ⟨[], Finset.mem_insert_self _ _⟩
      have := hy r
      unfold rootState at h
      rw [h] at this
      have h1 : run δY r y = r := (Prod.ext_iff.1 this).1.symm
      have h2 : p'.val = [] := by
        have := congrArg (fun s => s.2.val) this
        simp only at this
        exact this.symm
      refine ⟨y, h1, ?_⟩
      rw [h2] at hw
      simpa using hw
    · rintro ⟨y, hy, rfl⟩
      rw [rootState, cb_parse δY Z hPC e (subst (Z := lang Z) e y) ⟨[], Finset.mem_insert_self _ _⟩ y (by simp) r, hy, rootState]
  -- strong connectivity
  have hb : StronglyConnected δY → StronglyConnected (composeDecoder δY Z e) := by
    intro hSC s s'
    obtain ⟨q, p⟩ := s
    obtain ⟨q', p'⟩ := s'
    obtain ⟨z, hz, v, hv⟩ := cd_pp_prefix Z hZ p.val p.2
    obtain ⟨y, hy⟩ := hSC (run δY q [e.symm ⟨z, hz⟩]) q'
    refine ⟨v ++ subst (Z := lang Z) e y ++ p'.val, ?_⟩
    rw [cb_run_append, cb_run_append,
      cb_parse δY Z hPC e v p [e.symm ⟨z, hz⟩] (by rw [cb_subst_cons, cb_subst_nil]; simp [hv]) q,
      rootState, cb_parse δY Z hPC e (subst (Z := lang Z) e y) ⟨[], Finset.mem_insert_self _ _⟩ y (by simp), hy, rootState,
      cd_read δY Z hPC e q' p'.val ⟨[], Finset.mem_insert_self _ _⟩ (by simpa using p'.2)]
    simp
  refine ⟨?_, hb, ?_, fun r w => hc r w⟩
  · -- (a) counting
    have hnil : [] ∈ allPrefixes Z := by
      obtain ⟨z, hz⟩ := cd_nonempty Z hZ
      exact (cd_mem_all Z []).2 ⟨z, hz, List.nil_prefix⟩
    have hEq : allPrefixes Z = insert []
        (((properPrefixes Z) ×ˢ (Finset.univ : Finset α)).image fun px => px.1 ++ [px.2]) := by
      ext u
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_product, Finset.mem_univ,
        and_true, Prod.exists]
      constructor
      · intro hu
        rcases List.eq_nil_or_concat u with h | ⟨L, b, h⟩
        · exact Or.inl h
        · rw [List.concat_eq_append] at h
          subst h
          right
          refine ⟨L, b, ?_, rfl⟩
          rw [cd_mem_all] at hu
          obtain ⟨z, hz, hLz⟩ := hu
          rw [cd_mem_pp]
          by_cases hL : L = []
          · exact Or.inl hL
          · right
            have hLz' : L <+: z := (List.prefix_append _ _).trans hLz
            refine ⟨⟨z, hz, hLz'⟩, fun hLZ => ?_⟩
            have : L = z := hPC.2 L hLZ z hz hLz'
            have hl := hLz.length_le
            rw [← this] at hl
            simp at hl
      · rintro (rfl | ⟨p, x, hp, rfl⟩)
        · exact hnil
        · rcases cd_ext Z hZ p hp x with h | h
          · exact (cd_mem_all Z _).2 ⟨_, h, List.prefix_refl _⟩
          · rw [cd_mem_pp] at h
            rcases h with h | ⟨h, _⟩
            · simp at h
            · exact (cd_mem_all Z _).2 h
    have hinj : Set.InjOn (fun px : List α × α => px.1 ++ [px.2])
        ↑((properPrefixes Z) ×ˢ (Finset.univ : Finset α)) := by
      rintro ⟨a, x⟩ _ ⟨b, y⟩ _ h
      simp only at h
      obtain ⟨h1, h2⟩ := List.append_inj' h rfl
      simp only [List.cons.injEq, and_true] at h2
      rw [h1, h2]
    have hnot : [] ∉ ((properPrefixes Z) ×ˢ (Finset.univ : Finset α)).image
        fun px => px.1 ++ [px.2] := by
      simp
    have hcard : (allPrefixes Z).card = (properPrefixes Z).card * Fintype.card α + 1 := by
      rw [hEq, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hinj,
        Finset.card_product, Finset.card_univ]
    rw [hcard]
    simp only [DecoderState, Fintype.card_prod, Fintype.card_coe]
    ring
  · -- Huffman decoders
    rintro ⟨hSC, r, hfin⟩
    refine ⟨hb hSC, rootState Z r, ?_⟩
    apply Set.Finite.subset (hfin.image (subst (Z := lang Z) e))
    rintro w ⟨hw0, hwr, hwmin⟩
    obtain ⟨y, hyr, rfl⟩ := (hc r w).1 hwr
    refine ⟨y, ⟨?_, hyr, ?_⟩, rfl⟩
    · rintro rfl; exact hw0 (cb_subst_nil Z e)
    · intro i hi0 hi hret
      have hsplit := cd_subst_append Z e (y.take i) (y.drop i)
      rw [List.take_append_drop] at hsplit
      have hne1 := cd_subst_ne_nil Z hPC e (y.take i) (by
        intro h; rw [List.take_eq_nil_iff] at h
        rcases h with h | h
        · omega
        · subst h; simp at hi)
      have hne2 := cd_subst_ne_nil Z hPC e (y.drop i) (by
        intro h; rw [List.drop_eq_nil_iff] at h; omega)
      apply hwmin (subst (Z := lang Z) e (y.take i)).length
      · exact List.length_pos_iff.2 hne1
      · rw [hsplit, List.length_append]
        have := List.length_pos_iff.2 hne2
        omega
      · rw [hsplit, List.take_left]
        exact (hc r _).2 ⟨_, hret, rfl⟩
