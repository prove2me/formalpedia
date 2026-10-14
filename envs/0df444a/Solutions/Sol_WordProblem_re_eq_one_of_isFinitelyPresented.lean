-- Prove2me | solution 1 for WordProblem.re_eq_one_of_isFinitelyPresented
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-12T16:56:46.228386+00:00
-- url     : https://prove2.me/submissions/d293e577-63ca-4797-a543-0bd8db7ee1cb

import Mathlib
import Definitions.Def_BooneHigman

open OAI.FiniteAlgebraicEnvelopes

namespace WordProblem

universe u

/-! ### Part 0: generic helpers -/

/-- `evalWord` of a composed tuple is the image of `evalWord` under the homomorphism. -/
theorem evalWord_comp {G : Type} {H : Type u} [Group G] [Group H] (φ : G →* H) {n : ℕ}
    (tuple : Fin n → G) (word : Word n) :
    evalWord (φ ∘ tuple) word = φ (evalWord tuple word) := by
  classical
  unfold evalWord
  rw [map_list_prod]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro letter _
  by_cases h : letter.2 <;> simp [h, Function.comp_apply]

/-! ### Part 1: `FreeGroup.reduce` is primitive recursive. -/

variable {α : Type} [DecidableEq α] [Primcodable α]

def stepCore (p : (α × Bool) × List (α × Bool)) : List (α × Bool) :=
  List.casesOn p.2 [p.1] (fun hd tl => if p.1.1 = hd.1 ∧ p.1.2 = !hd.2 then tl else p.1 :: hd :: tl)

theorem stepCore_primrec : Primrec (stepCore (α := α)) := by
  unfold stepCore
  apply Primrec.list_casesOn (f := fun p : (α × Bool) × List (α × Bool) => p.2)
    (g := fun p : (α × Bool) × List (α × Bool) => [p.1])
    (h := fun (p q : (α × Bool) × List (α × Bool)) =>
      if p.1.1 = q.1.1 ∧ p.1.2 = !q.1.2 then q.2 else p.1 :: q.1 :: q.2)
  · exact Primrec.snd
  · exact Primrec.list_cons.comp Primrec.fst (Primrec.const [])
  · have e1 : PrimrecRel (fun (p q : (α × Bool) × List (α × Bool)) => p.1.1 = q.1.1) :=
      Primrec.eq.comp₂ (Primrec.fst.comp₂ (Primrec.fst.comp₂ Primrec₂.left))
        (Primrec.fst.comp₂ (Primrec.fst.comp₂ Primrec₂.right))
    have e2 : PrimrecRel (fun (p q : (α × Bool) × List (α × Bool)) => p.1.2 = !q.1.2) :=
      Primrec.eq.comp₂ (Primrec.snd.comp₂ (Primrec.fst.comp₂ Primrec₂.left))
        (Primrec.not.comp (Primrec.snd.comp₂ (Primrec.fst.comp₂ Primrec₂.right)))
    have hcond : PrimrecPred (fun (pr : ((α × Bool) × List (α × Bool)) ×
        ((α × Bool) × List (α × Bool))) => pr.1.1.1 = pr.2.1.1 ∧ pr.1.1.2 = !pr.2.1.2) :=
      PrimrecPred.and e1 e2
    apply Primrec.ite hcond
    · exact Primrec.snd.comp Primrec.snd
    · exact Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

omit [Primcodable α] in
theorem reduce_eq_foldr (L : List (α × Bool)) :
    FreeGroup.reduce L = L.foldr (fun b s => stepCore (b, s)) [] := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [FreeGroup.reduce.cons, List.foldr_cons, ← ih]
    rfl

theorem primrec_reduce : Primrec (FreeGroup.reduce : List (α × Bool) → List (α × Bool)) := by
  have := Primrec.list_foldr (f := @id (List (α × Bool)))
    (g := fun _ : List (α × Bool) => ([] : List (α × Bool)))
    (h := fun (_ : List (α × Bool)) (q : (α × Bool) × List (α × Bool)) => stepCore q)
    Primrec.id (Primrec.const [])
    (stepCore_primrec.comp Primrec.snd)
  exact this.of_eq (fun L => (reduce_eq_foldr L).symm)

/-! ### Part 2: raw-word evaluators, connected to `evalWord`/group arithmetic via `FreeGroup.mk`. -/

/-- A raw-word (concatenation-based) evaluator over `List (α × Bool)`, mirroring `evalWord` but
staying at the level of free-group representatives instead of group elements. -/
def rawEval {m : ℕ} (gens : Fin m → List (α × Bool)) (word : Word m) : List (α × Bool) :=
  (word.map (fun l => if l.2 then gens l.1 else FreeGroup.invRev (gens l.1))).flatten

omit [DecidableEq α] [Primcodable α] in
theorem mk_rawEval {m : ℕ} (gens : Fin m → List (α × Bool)) (word : Word m) :
    FreeGroup.mk (rawEval gens word) = evalWord (fun i => FreeGroup.mk (gens i)) word := by
  unfold rawEval
  induction word with
  | nil => simp [evalWord, ← FreeGroup.one_eq_mk]
  | cons a rest ih =>
    rw [List.map_cons, List.flatten_cons, ← FreeGroup.mul_mk, ih]
    unfold evalWord
    by_cases h : a.2 <;> simp [h, FreeGroup.inv_mk]

/-- A conjugate-products evaluator (same shape as `certEval`, below), at the raw-word level. -/
def rawCertEval {ι : Type*} (relWord : ι → List (α × Bool))
    (cert : List (List (α × Bool) × Bool × ι)) : List (α × Bool) :=
  (cert.map (fun t => t.1 ++ (if t.2.1 then relWord t.2.2 else FreeGroup.invRev (relWord t.2.2))
    ++ FreeGroup.invRev t.1)).flatten

/-- A finite product of conjugates of relators (or their inverses): the group-theoretic
companion to `rawCertEval`. -/
def certEval {G : Type u} [Group G] {ι : Type*} (relators : ι → G)
    (cert : List (G × Bool × ι)) : G :=
  (cert.map (fun t => t.1 * (if t.2.1 then relators t.2.2 else (relators t.2.2)⁻¹) * t.1⁻¹)).prod

omit [DecidableEq α] [Primcodable α] in
theorem mk_rawCertEval {ι : Type*} (relWord : ι → List (α × Bool))
    (cert : List (List (α × Bool) × Bool × ι)) :
    FreeGroup.mk (rawCertEval relWord cert) =
      certEval (fun i => FreeGroup.mk (relWord i))
        (cert.map (fun t => (FreeGroup.mk t.1, t.2.1, t.2.2))) := by
  unfold rawCertEval certEval
  induction cert with
  | nil => simp [← FreeGroup.one_eq_mk]
  | cons a rest ih =>
    simp only [List.map_cons, List.flatten_cons, List.prod_cons]
    rw [← FreeGroup.mul_mk, ih]
    congr 1
    rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
    by_cases h : a.2.1 <;> simp [h, FreeGroup.inv_mk]

/-! ### Part 3: `normalClosure` membership as a finite product of conjugates. -/

theorem certEval_inv {G : Type u} [Group G] {ι : Type*} (relators : ι → G)
    (cert : List (G × Bool × ι)) :
    certEval relators (cert.reverse.map (fun t => (t.1, !t.2.1, t.2.2))) =
      (certEval relators cert)⁻¹ := by
  induction cert with
  | nil => simp [certEval]
  | cons a rest ih =>
    rw [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
    have hsplit : certEval relators (rest.reverse.map (fun t => (t.1, !t.2.1, t.2.2)) ++
        [(a.1, !a.2.1, a.2.2)]) =
        certEval relators (rest.reverse.map (fun t => (t.1, !t.2.1, t.2.2))) *
          certEval relators [(a.1, !a.2.1, a.2.2)] := by
      unfold certEval
      rw [List.map_append, List.prod_append]
    rw [hsplit, ih]
    unfold certEval
    by_cases h : a.2.1 <;> simp [h, mul_inv_rev, mul_assoc]

theorem exists_cert_of_mem_normalClosure {G : Type u} [Group G] {ι : Type*} (relators : ι → G)
    (x : G) (hx : x ∈ Subgroup.normalClosure (Set.range relators)) :
    ∃ cert : List (G × Bool × ι), x = certEval relators cert := by
  unfold Subgroup.normalClosure at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hy
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    exact ⟨[(c, true, i)], by simp [certEval, hc]⟩
  | one => exact ⟨[], by simp [certEval]⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨cx, hcx⟩ := ihx
    obtain ⟨cy, hcy⟩ := ihy
    refine ⟨cx ++ cy, ?_⟩
    unfold certEval
    rw [List.map_append, List.prod_append]
    unfold certEval at hcx hcy
    rw [hcx, hcy]
  | inv x _ ihx =>
    obtain ⟨cx, hcx⟩ := ihx
    exact ⟨cx.reverse.map (fun t => (t.1, !t.2.1, t.2.2)), by rw [certEval_inv, ← hcx]⟩

theorem certEval_mem_normalClosure {G : Type u} [Group G] {ι : Type*} (relators : ι → G)
    (cert : List (G × Bool × ι)) :
    certEval relators cert ∈ Subgroup.normalClosure (Set.range relators) := by
  unfold certEval
  induction cert with
  | nil => simp
  | cons a rest ih =>
    rw [List.map_cons, List.prod_cons]
    refine Subgroup.mul_mem _ ?_ ih
    have hmem : relators a.2.2 ∈ Subgroup.normalClosure (Set.range relators) :=
      Subgroup.subset_normalClosure ⟨a.2.2, rfl⟩
    have hmem' : (if a.2.1 then relators a.2.2 else (relators a.2.2)⁻¹) ∈
        Subgroup.normalClosure (Set.range relators) := by
      by_cases h : a.2.1 <;> simp [h, hmem, Subgroup.inv_mem _ hmem]
    exact Subgroup.normalClosure_normal.conj_mem _ hmem' a.1

theorem mem_normalClosure_iff_exists_cert {G : Type u} [Group G] {ι : Type*} (relators : ι → G)
    (x : G) :
    x ∈ Subgroup.normalClosure (Set.range relators) ↔
      ∃ cert : List (G × Bool × ι), x = certEval relators cert :=
  ⟨exists_cert_of_mem_normalClosure relators x, fun ⟨cert, hcert⟩ =>
    hcert ▸ certEval_mem_normalClosure relators cert⟩

/-! ### Part 4: a general `REPred` existence combinator. -/

theorem REPred.of_exists {β : Type*} [Denumerable β] {γ : Type*} [Primcodable γ]
    {R : γ → β → Prop} (hR : ComputablePred (fun p : γ × β => R p.1 p.2)) :
    REPred (fun a => ∃ b, R a b) := by
  classical
  have hdec : Computable (fun p : γ × β => decide (R p.1 p.2)) := hR.decide
  have hcomp : Computable (fun p : γ × ℕ => decide (R p.1 (Denumerable.ofNat β p.2))) :=
    hdec.comp (Computable.pair Computable.fst (Computable.ofNat β |>.comp Computable.snd))
  let g : γ → ℕ →. Bool := fun a k => Part.some (decide (R a (Denumerable.ofNat β k)))
  have hg : Partrec₂ g := by
    have : Partrec₂ (fun (a : γ) => ((fun k => decide (R a (Denumerable.ofNat β k))) :
        ℕ →. Bool)) := hcomp.to₂.partrec₂
    exact this.of_eq (fun ⟨a, k⟩ => rfl)
  have hf : Partrec (fun a : γ => Nat.rfind (g a)) := Partrec.rfind hg
  have hre : REPred (fun a : γ => (Nat.rfind (g a)).Dom) := Partrec.dom_re hf
  refine hre.of_eq (fun a => ?_)
  show (Nat.rfind (g a)).Dom ↔ ∃ b, R a b
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨n, hn, -⟩
    simp only [g, Part.mem_some_iff] at hn
    exact ⟨Denumerable.ofNat β n, by simpa using hn.symm⟩
  · rintro ⟨b, hb⟩
    refine ⟨Encodable.encode b, ?_, fun _ => trivial⟩
    simp [g, Denumerable.ofNat_encode, hb]

set_option maxHeartbeats 1000000 in
/-- Isolated, reusable helper: if `(x, y) ↦ P x y` is computable, so is the existential-via-decode
wrapping used to search over an `Encodable` type `β` by its `ℕ`-encoding. Kept as its own
top-level lemma (rather than inlined) because its `Computable.option_casesOn` elaboration is
expensive and must not carry the large context of its caller. -/
theorem computable_option_elim_decide {α : Type} [Primcodable α] {β : Type} [Primcodable β]
    {P : α → β → Prop} [DecidableRel P]
    (hP : Computable (fun pr : α × β => decide (P pr.1 pr.2))) :
    Computable (fun pr : α × ℕ => Option.elim (Encodable.decode pr.2 : Option β) false
      (fun y => decide (P pr.1 y))) := by
  have h := Computable.option_casesOn (o := fun pr : α × ℕ => (Encodable.decode pr.2 : Option β))
    (f := fun _ : α × ℕ => false)
    (g := fun (pr : α × ℕ) (y : β) => decide (P pr.1 y))
    (Computable.decode.comp Computable.snd) (Computable.const false)
    (hP.comp (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd))
  exact h.of_eq (fun pr => by
    rcases hd : (Encodable.decode pr.2 : Option β) with _ | y <;> simp)

/-! ### Part 5: assembling Fact C1. -/

end WordProblem

universe u

open OAI.FiniteAlgebraicEnvelopes WordProblem in
set_option maxHeartbeats 1000000 in
theorem solution {H : Type u} [Group H] [Group.IsFinitelyPresented H]
    {n : ℕ} (p : Fin n → H) (_hp : Subgroup.closure (Set.range p) = ⊤) :
    REPred (fun word : Word n => evalWord p word = 1) := by
  classical
  obtain ⟨k, π, hπsurj, S, hSfin, hSker⟩ := ‹Group.IsFinitelyPresented H›.out
  -- a finite tuple enumerating `insert 1 S` (always nonempty, so its cardinality is ≥ 1)
  obtain ⟨relSet0, hrSubset0⟩ := hSfin.exists_finset_coe
  set relSet := insert (1 : FreeGroup (Fin k)) relSet0 with hrelSet_def
  have hrpos : 0 < relSet.card :=
    Finset.card_pos.2 ⟨1, Finset.mem_insert_self _ _⟩
  set r := relSet.card with hr_def
  let e : Fin r ≃ relSet := (Fintype.equivFinOfCardEq (α := relSet) (Fintype.card_coe relSet)).symm
  let relators : Fin r → FreeGroup (Fin k) := fun i => ((e i : relSet) : FreeGroup (Fin k))
  have hrange : Set.range relators = insert (1 : FreeGroup (Fin k)) S := by
    apply Set.eq_of_subset_of_subset
    · rintro _ ⟨i, rfl⟩
      have hmem : (e i : FreeGroup (Fin k)) ∈ relSet := (e i).2
      simp only [hrelSet_def, Finset.mem_insert] at hmem
      rcases hmem with h1 | h2
      · exact Set.mem_insert_iff.2 (Or.inl h1)
      · exact Set.mem_insert_iff.2 (Or.inr (hrSubset0 ▸ Finset.mem_coe.2 h2))
    · intro x hx
      rcases Set.mem_insert_iff.1 hx with rfl | hxS
      · exact ⟨e.symm ⟨1, by simp [hrelSet_def]⟩, by simp [relators]⟩
      · have hx' : x ∈ relSet := by
          simp only [hrelSet_def, Finset.mem_insert]
          exact Or.inr (Finset.mem_coe.1 (hrSubset0 ▸ hxS))
        exact ⟨e.symm ⟨x, hx'⟩, by simp [relators]⟩
  have hnormal : Subgroup.normalClosure (Set.range relators) = π.ker := by
    rw [hrange]
    have h1 : Subgroup.normalClosure ({1} : Set (FreeGroup (Fin k))) = ⊥ :=
      Subgroup.normalClosure_eq_bot_iff.2 (le_refl _)
    rw [show insert (1 : FreeGroup (Fin k)) S = ({1} : Set (FreeGroup (Fin k))) ∪ S from rfl,
      Subgroup.normalClosure_union, h1, bot_sup_eq, hSker]
  -- preimages of `p`'s generators under `π`
  choose q hq using fun i => hπsurj (p i)
  let qWord : Fin n → List (Fin k × Bool) := fun i => FreeGroup.toWord (q i)
  let relWord : Fin r → List (Fin k × Bool) := fun i => FreeGroup.toWord (relators i)
  have hqWord : ∀ i, FreeGroup.mk (qWord i) = q i := fun _ => FreeGroup.mk_toWord
  have hrelWord : ∀ i, FreeGroup.mk (relWord i) = relators i := fun _ => FreeGroup.mk_toWord
  have hiff : ∀ word : Word n, evalWord p word = 1 ↔
      ∃ cert : List (List (Fin k × Bool) × Bool × Fin r),
        FreeGroup.mk (rawEval qWord word) = FreeGroup.mk (rawCertEval relWord cert) := by
    intro word
    have step1 : evalWord p word = 1 ↔ π (evalWord q word) = 1 := by
      rw [← evalWord_comp π q word, show (π ∘ q) = p from funext hq]
    have step2 : π (evalWord q word) = 1 ↔ evalWord q word ∈ π.ker := by
      rw [MonoidHom.mem_ker]
    have step3 : evalWord q word ∈ π.ker ↔
        evalWord q word ∈ Subgroup.normalClosure (Set.range relators) := by
      rw [hnormal]
    have step5 := mem_normalClosure_iff_exists_cert relators (evalWord q word)
    rw [step1, step2, step3, step5]
    have hcert_simp : ∀ (cert : List (FreeGroup (Fin k) × Bool × Fin r)),
        cert.map (fun t => (FreeGroup.mk t.1.toWord, t.2.1, t.2.2)) = cert := by
      intro cert
      conv_rhs => rw [← List.map_id cert]
      apply List.map_congr_left
      intro t _
      simp [FreeGroup.mk_toWord]
    constructor
    · rintro ⟨cert, hcert⟩
      refine ⟨cert.map (fun t => (FreeGroup.toWord t.1, t.2.1, t.2.2)), ?_⟩
      rw [mk_rawEval, mk_rawCertEval, List.map_map]
      rw [show ((fun t => (FreeGroup.mk t.1, t.2.1, t.2.2)) ∘
          (fun t : FreeGroup (Fin k) × Bool × Fin r => (t.1.toWord, t.2.1, t.2.2))) =
          (fun t => (FreeGroup.mk t.1.toWord, t.2.1, t.2.2)) from rfl]
      rw [hcert_simp cert, funext hqWord, funext hrelWord]
      exact hcert
    · rintro ⟨cert, hcert⟩
      refine ⟨cert.map (fun t => (FreeGroup.mk t.1, t.2.1, t.2.2)), ?_⟩
      rw [mk_rawEval, mk_rawCertEval, funext hqWord, funext hrelWord] at hcert
      exact hcert
  have hre : ∀ (w1 w2 : List (Fin k × Bool)),
      FreeGroup.mk w1 = FreeGroup.mk w2 ↔ FreeGroup.reduce w1 = FreeGroup.reduce w2 :=
    fun w1 w2 => ⟨FreeGroup.reduce.sound, FreeGroup.reduce.exact⟩
  -- Primrec plumbing for `rawEval`/`rawCertEval` over the fixed tables `qWord`/`relWord`.
  have hrawEval_primrec : Primrec (fun pr : Word n × List (List (Fin k × Bool) × Bool × Fin r) =>
      rawEval qWord pr.1) := by
    have hq_primrec : Primrec qWord := Primrec.fin_app.comp (Primrec.const qWord) Primrec.id
    have hflip_primrec : Primrec (fun l : Fin k × Bool => (l.1, !l.2)) :=
      Primrec.pair Primrec.fst (Primrec.not.comp Primrec.snd)
    have hinvRev_primrec : Primrec (fun w : List (Fin k × Bool) => FreeGroup.invRev w) := by
      show Primrec (fun w : List (Fin k × Bool) => (w.map (fun l => (l.1, !l.2))).reverse)
      exact Primrec.list_reverse.comp (Primrec.list_map Primrec.id (hflip_primrec.comp Primrec.snd))
    have hcond_letter : PrimrecPred (fun letter : Fin n × Bool => letter.2 = true) :=
      Primrec.eq.comp Primrec.snd (Primrec.const true)
    have hletter_primrec : Primrec (fun letter : Fin n × Bool => if letter.2 then qWord letter.1
        else FreeGroup.invRev (qWord letter.1)) :=
      Primrec.ite hcond_letter (hq_primrec.comp Primrec.fst)
        (hinvRev_primrec.comp (hq_primrec.comp Primrec.fst))
    have hmap_primrec : Primrec (fun word : Word n => word.map (fun letter =>
        if letter.2 then qWord letter.1 else FreeGroup.invRev (qWord letter.1))) :=
      Primrec.list_map Primrec.id (hletter_primrec.comp Primrec.snd)
    have hflatten_primrec : Primrec (fun word : Word n => rawEval qWord word) :=
      Primrec.list_flatten.comp hmap_primrec
    exact hflatten_primrec.comp Primrec.fst
  have hrawCertEval_primrec : Primrec (fun pr : Word n ×
      List (List (Fin k × Bool) × Bool × Fin r) => rawCertEval relWord pr.2) := by
    have hrel_primrec : Primrec relWord := Primrec.fin_app.comp (Primrec.const relWord) Primrec.id
    have hflip_primrec : Primrec (fun l : Fin k × Bool => (l.1, !l.2)) :=
      Primrec.pair Primrec.fst (Primrec.not.comp Primrec.snd)
    have hinvRev_primrec : Primrec (fun w : List (Fin k × Bool) => FreeGroup.invRev w) := by
      show Primrec (fun w : List (Fin k × Bool) => (w.map (fun l => (l.1, !l.2))).reverse)
      exact Primrec.list_reverse.comp (Primrec.list_map Primrec.id (hflip_primrec.comp Primrec.snd))
    have hcond_triple : PrimrecPred (fun t : List (Fin k × Bool) × Bool × Fin r => t.2.1 = true) :=
      Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const true)
    have htriple_primrec : Primrec (fun t : List (Fin k × Bool) × Bool × Fin r =>
        t.1 ++ (if t.2.1 then relWord t.2.2 else FreeGroup.invRev (relWord t.2.2)) ++
          FreeGroup.invRev t.1) := by
      have hmid : Primrec (fun t : List (Fin k × Bool) × Bool × Fin r =>
          if t.2.1 then relWord t.2.2 else FreeGroup.invRev (relWord t.2.2)) :=
        Primrec.ite hcond_triple
          (hrel_primrec.comp (Primrec.snd.comp Primrec.snd))
          (hinvRev_primrec.comp (hrel_primrec.comp (Primrec.snd.comp Primrec.snd)))
      exact Primrec.list_append.comp
        (Primrec.list_append.comp Primrec.fst hmid)
        (hinvRev_primrec.comp Primrec.fst)
    have hmap_primrec : Primrec (fun cert : List (List (Fin k × Bool) × Bool × Fin r) =>
        cert.map (fun t => t.1 ++ (if t.2.1 then relWord t.2.2 else FreeGroup.invRev (relWord t.2.2))
          ++ FreeGroup.invRev t.1)) :=
      Primrec.list_map Primrec.id (htriple_primrec.comp Primrec.snd)
    have hflatten_primrec : Primrec (fun cert : List (List (Fin k × Bool) × Bool × Fin r) =>
        rawCertEval relWord cert) := Primrec.list_flatten.comp hmap_primrec
    exact hflatten_primrec.comp Primrec.snd
  have hreduce_comp1 : Primrec (fun pr : Word n × List (List (Fin k × Bool) × Bool × Fin r) =>
      FreeGroup.reduce (rawEval qWord pr.1)) := primrec_reduce.comp hrawEval_primrec
  have hreduce_comp2 : Primrec (fun pr : Word n × List (List (Fin k × Bool) × Bool × Fin r) =>
      FreeGroup.reduce (rawCertEval relWord pr.2)) := primrec_reduce.comp hrawCertEval_primrec
  have hcertEqDec : Primrec (fun pr : Word n × List (List (Fin k × Bool) × Bool × Fin r) =>
      decide (FreeGroup.reduce (rawEval qWord pr.1) = FreeGroup.reduce (rawCertEval relWord pr.2))) :=
    (Primrec.eq.comp hreduce_comp1 hreduce_comp2).decide
  have hcert_eq_comp : Computable (fun pr : Word n × List (List (Fin k × Bool) × Bool × Fin r) =>
      decide (FreeGroup.mk (rawEval qWord pr.1) = FreeGroup.mk (rawCertEval relWord pr.2))) :=
    hcertEqDec.to_comp.of_eq (fun pr => decide_eq_decide.mpr (hre _ _).symm)
  -- bridge: existence over certificates is equivalent to existence over `ℕ`, via `decode`.
  have hiff2 : ∀ word : Word n,
      (∃ cert : List (List (Fin k × Bool) × Bool × Fin r),
        FreeGroup.mk (rawEval qWord word) = FreeGroup.mk (rawCertEval relWord cert)) ↔
      ∃ nIdx : ℕ, Option.elim (Encodable.decode nIdx :
          Option (List (List (Fin k × Bool) × Bool × Fin r))) False
        (fun cert => FreeGroup.mk (rawEval qWord word) = FreeGroup.mk (rawCertEval relWord cert)) := by
    intro word
    constructor
    · rintro ⟨cert, hcert⟩
      refine ⟨Encodable.encode cert, ?_⟩
      rw [Encodable.encodek]
      exact hcert
    · rintro ⟨nIdx, hnIdx⟩
      rcases hd : (Encodable.decode nIdx :
          Option (List (List (Fin k × Bool) × Bool × Fin r))) with _ | cert
      · rw [hd] at hnIdx; exact absurd hnIdx id
      · rw [hd] at hnIdx; exact ⟨cert, hnIdx⟩
  refine (REPred.of_exists (γ := Word n) (β := ℕ)
      (R := fun (word : Word n) (nIdx : ℕ) =>
        Option.elim (Encodable.decode nIdx :
            Option (List (List (Fin k × Bool) × Bool × Fin r))) False
          (fun cert => FreeGroup.mk (rawEval qWord word) = FreeGroup.mk (rawCertEval relWord cert)))
      ?_).of_eq (fun word => by rw [← hiff2 word]; exact (hiff word).symm)
  refine ⟨fun pr => by classical infer_instance, ?_⟩
  have hfinal := computable_option_elim_decide
    (P := fun (word : Word n) (cert : List (List (Fin k × Bool) × Bool × Fin r)) =>
      FreeGroup.mk (rawEval qWord word) = FreeGroup.mk (rawCertEval relWord cert))
    hcert_eq_comp
  exact hfinal.of_eq (fun pr => by
    rcases h : (Encodable.decode pr.2 :
        Option (List (List (Fin k × Bool) × Bool × Fin r))) with _ | cert <;> simp [h])

