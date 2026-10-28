-- Prove2me | solution 1 for SyncPrefix.Huffman.composition_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-26T22:45:51.602765+00:00
-- url     : https://prove2.me/submissions/9bc73f82-cc72-4d51-8780-90608920ff55

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

end CB

theorem solution {σ α β : Type} [DecidableEq α] (δY : σ → β → σ)
    (Z : Finset (List α)) (hZ : IsMaximalPrefixCode (lang Z)) (e : β ≃ {z // z ∈ Z})
    (m M : ℕ) (hm : IsLeast ((fun z : List α => z.length) '' (Z : Set (List α))) m)
    (hM : IsGreatest ((fun z : List α => z.length) '' (Z : Set (List α))) M)
    (wZ : List α) (hwZ : ∀ u : List α, u ++ wZ ∈ (lang Z)∗) (hY : IsSynchronizing δY) :
    IsSynchronizing (composeDecoder δY Z e) ∧
      m * syncLength δY ≤ syncLength (composeDecoder δY Z e) ∧
      syncLength (composeDecoder δY Z e) ≤ M * syncLength δY + wZ.length := by
  have hPC := hZ.1
  have hmb : ∀ b, m ≤ (e b).val.length := fun b => hm.2 ⟨(e b).val, (e b).2, rfl⟩
  have hMb : ∀ b, (e b).val.length ≤ M := fun b => hM.2 ⟨(e b).val, (e b).2, rfl⟩
  -- a shortest synchronizing word of `δY`
  obtain ⟨y, hylen, r, hyr⟩ : ∃ y : List β, y.length = syncLength δY ∧ IsSyncWord δY y :=
    Nat.sInf_mem (s := {ℓ | ∃ w : List β, w.length = ℓ ∧ IsSyncWord δY w})
      (by obtain ⟨w, hw⟩ := hY; exact ⟨_, w, rfl, hw⟩)
  -- the word `wZ β(y)` synchronizes the decoder
  have hsyncX : IsSyncWord (composeDecoder δY Z e) (wZ ++ subst (Z := lang Z) e y) := by
    refine ⟨rootState Z r, fun s => ?_⟩
    obtain ⟨q, p⟩ := s
    obtain ⟨L, hL, hLmem⟩ := Language.mem_kstar.1 (hwZ p.val)
    obtain ⟨zs, hzs⟩ := cb_flatten Z e L (fun z hz => (cb_mem_lang Z z).1 (hLmem z hz))
    rw [cb_run_append, cb_parse δY Z hPC e wZ p zs (by rw [hzs, hL]) q]
    have := cb_parse δY Z hPC e (subst (Z := lang Z) e y) ⟨[], Finset.mem_insert_self _ _⟩ y
      (by simp) (run δY q zs)
    unfold rootState at this ⊢
    rw [this, hyr]
  have hupper : syncLength (composeDecoder δY Z e) ≤ M * syncLength δY + wZ.length := by
    have h1 : syncLength (composeDecoder δY Z e) ≤ (wZ ++ subst (Z := lang Z) e y).length :=
      Nat.sInf_le ⟨_, rfl, hsyncX⟩
    have h2 := cb_subst_len Z e M hMb y
    rw [List.length_append] at h1
    rw [← hylen]
    omega
  refine ⟨⟨_, hsyncX⟩, ?_, hupper⟩
  -- lower bound
  obtain ⟨w, hwlen, s, hws⟩ : ∃ w : List α, w.length = syncLength (composeDecoder δY Z e) ∧
      IsSyncWord (composeDecoder δY Z e) w :=
    Nat.sInf_mem (s := {ℓ | ∃ w : List α, w.length = ℓ ∧ IsSyncWord (composeDecoder δY Z e) w})
      ⟨_, _, rfl, hsyncX⟩
  obtain ⟨y', p', hy', hlen⟩ := cb_lower δY Z e m hmb w ⟨[], Finset.mem_insert_self _ _⟩
  have hsy' : IsSyncWord δY y' := by
    refine ⟨s.1, fun q => ?_⟩
    have := hws (q, ⟨[], Finset.mem_insert_self _ _⟩)
    rw [hy' q] at this
    rw [← this]
  have h1 : syncLength δY ≤ y'.length := Nat.sInf_le ⟨_, rfl, hsy'⟩
  simp only [List.length_nil, zero_add] at hlen
  rw [← hwlen]
  calc m * syncLength δY ≤ m * y'.length := Nat.mul_le_mul_left _ h1
    _ ≤ w.length := by omega
