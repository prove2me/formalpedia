-- Prove2me | solution 1 for WordProblem.re_ne_one_of_isFinitelyPresented_simple
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-12T17:25:49.354036+00:00
-- url     : https://prove2.me/submissions/0e9d148e-a76a-4310-b068-62d12954a223

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


/-- Inserting the identity into a generating set does not change its normal closure. -/
theorem normalClosure_insert_one {G : Type u} [Group G] (S : Set G) :
    Subgroup.normalClosure (insert (1 : G) S) = Subgroup.normalClosure S := by
  have h1 : Subgroup.normalClosure ({1} : Set G) = ⊥ :=
    Subgroup.normalClosure_eq_bot_iff.2 (le_refl _)
  rw [show insert (1 : G) S = ({1} : Set G) ∪ S from rfl,
    Subgroup.normalClosure_union, h1, bot_sup_eq]

/-- The preimage, under a surjective homomorphism, of the normal closure of a singleton equals
the normal closure of (a preimage of that element, together with the kernel's own generators),
provided the kernel is itself the normal closure of those generators. -/
theorem comap_normalClosure_singleton {G : Type} {H : Type u} [Group G] [Group H] (π : G →* H)
    (hπsurj : Function.Surjective π) (S : Set G) (hSker : Subgroup.normalClosure S = π.ker)
    (x : H) (xFree : G) (hxFree : π xFree = x) :
    (Subgroup.normalClosure ({x} : Set H)).comap π =
      Subgroup.normalClosure (insert xFree S) := by
  have hmap : (Subgroup.normalClosure (insert xFree S)).map π =
      Subgroup.normalClosure ({x} : Set H) := by
    rw [Subgroup.map_normalClosure _ π hπsurj, Set.image_insert_eq, hxFree]
    have himg : π '' S ⊆ ({1} : Set H) := by
      rintro _ ⟨s, hs, rfl⟩
      have : s ∈ π.ker := hSker ▸ Subgroup.subset_normalClosure hs
      simpa [MonoidHom.mem_ker] using this
    have : insert x (π '' S) = insert x ({1} : Set H) ∨ π '' S = ∅ := by
      rcases Set.eq_empty_or_nonempty (π '' S) with h | h
      · right; exact h
      · left
        obtain ⟨y, hy⟩ := h
        have : y = 1 := himg hy
        congr 1
        apply Set.eq_of_subset_of_subset
        · rintro z hz
          have : z = 1 := himg hz
          simp [this]
        · rintro z hz
          simp only [Set.mem_singleton_iff] at hz
          rw [hz, ← this]
          exact hy
    rcases this with h | h
    · rw [h, show ({x, 1} : Set H) = insert (1 : H) {x} from by ext; simp; tauto,
        normalClosure_insert_one]
    · simp [h]
  have hle : Subgroup.normalClosure S ≤ Subgroup.normalClosure (insert xFree S) :=
    Subgroup.normalClosure_mono (Set.subset_insert _ _)
  rw [hSker] at hle
  calc (Subgroup.normalClosure ({x} : Set H)).comap π
      = ((Subgroup.normalClosure (insert xFree S)).map π).comap π := by rw [hmap]
    _ = Subgroup.normalClosure (insert xFree S) ⊔ π.ker := Subgroup.comap_map_eq _ _
    _ = Subgroup.normalClosure (insert xFree S) := sup_eq_left.2 hle
end WordProblem

universe u

open OAI.FiniteAlgebraicEnvelopes WordProblem in
set_option maxHeartbeats 1000000 in
theorem solution {H : Type u} [Group H]
    [Group.IsFinitelyPresented H] [IsSimpleGroup H]
    {n : ℕ} (p : Fin n → H) (_hp : Subgroup.closure (Set.range p) = ⊤) :
    REPred (fun word : Word n => evalWord p word ≠ 1) := by
  classical
  obtain ⟨k, π, hπsurj, S, hSfin, hSker⟩ := ‹Group.IsFinitelyPresented H›.out
  obtain ⟨relSet0, hrSubset0⟩ := hSfin.exists_finset_coe
  set relSet := insert (1 : FreeGroup (Fin k)) relSet0 with hrelSet_def
  have hrpos : 0 < relSet.card := Finset.card_pos.2 ⟨1, Finset.mem_insert_self _ _⟩
  set r := relSet.card with hr_def
  let e : Fin r ≃ relSet := (Fintype.equivFinOfCardEq (α := relSet) (Fintype.card_coe relSet)).symm
  let relators0 : Fin r → FreeGroup (Fin k) := fun i => ((e i : relSet) : FreeGroup (Fin k))
  have hrange0 : Set.range relators0 = insert (1 : FreeGroup (Fin k)) S := by
    apply Set.eq_of_subset_of_subset
    · rintro _ ⟨i, rfl⟩
      have hmem : (e i : FreeGroup (Fin k)) ∈ relSet := (e i).2
      simp only [hrelSet_def, Finset.mem_insert] at hmem
      rcases hmem with h1 | h2
      · exact Set.mem_insert_iff.2 (Or.inl h1)
      · exact Set.mem_insert_iff.2 (Or.inr (hrSubset0 ▸ Finset.mem_coe.2 h2))
    · intro x hx
      rcases Set.mem_insert_iff.1 hx with rfl | hxS
      · exact ⟨e.symm ⟨1, by simp [hrelSet_def]⟩, by simp [relators0]⟩
      · have hx' : x ∈ relSet := by
          simp only [hrelSet_def, Finset.mem_insert]
          exact Or.inr (Finset.mem_coe.1 (hrSubset0 ▸ hxS))
        exact ⟨e.symm ⟨x, hx'⟩, by simp [relators0]⟩
  choose q hq using fun i => hπsurj (p i)
  let qWord : Fin n → List (Fin k × Bool) := fun i => FreeGroup.toWord (q i)
  let relWord0 : Fin r → List (Fin k × Bool) := fun i => FreeGroup.toWord (relators0 i)
  have hqWord : ∀ i, FreeGroup.mk (qWord i) = q i := fun _ => FreeGroup.mk_toWord
  have hrelWord0 : ∀ i, FreeGroup.mk (relWord0 i) = relators0 i := fun _ => FreeGroup.mk_toWord
  -- The mathematical equivalence, over `FreeGroup`-valued certificates for the extended family.
  have hiff : ∀ word : Word n, evalWord p word ≠ 1 ↔
      ∀ i : Fin n, ∃ cert : List (FreeGroup (Fin k) × Bool × Fin (r + 1)),
        q i = certEval (Fin.snoc relators0 (evalWord q word)) cert := by
    intro word
    set x := evalWord p word with hx_def
    set xFree := evalWord q word with hxFree_def
    have hxFreeEq : π xFree = x := by
      rw [hxFree_def, hx_def, ← evalWord_comp π q word, show (π ∘ q) = p from funext hq]
    have hrange_ext : Set.range (Fin.snoc relators0 xFree : Fin (r + 1) → FreeGroup (Fin k)) =
        insert xFree (Set.range relators0) := by
      ext z
      simp only [Set.mem_range, Set.mem_insert_iff]
      constructor
      · rintro ⟨i, rfl⟩
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · right; exact ⟨j, by simp [Fin.snoc_castSucc]⟩
        · left; simp [Fin.snoc_last]
      · rintro (rfl | ⟨i, rfl⟩)
        · exact ⟨Fin.last r, by simp [Fin.snoc_last]⟩
        · exact ⟨Fin.castSucc i, by simp [Fin.snoc_castSucc]⟩
    have hclosure_ext : Subgroup.normalClosure
        (Set.range (Fin.snoc relators0 xFree : Fin (r + 1) → FreeGroup (Fin k))) =
        Subgroup.normalClosure (insert xFree S) := by
      rw [hrange_ext, hrange0, show insert xFree (insert (1 : FreeGroup (Fin k)) S) =
          insert (1 : FreeGroup (Fin k)) (insert xFree S) from by ext; simp; tauto,
        normalClosure_insert_one]
    have hcomap := comap_normalClosure_singleton π hπsurj S hSker x xFree hxFreeEq
    constructor
    · intro hxne i
      have hne_closure : Subgroup.normalClosure ({x} : Set H) = ⊤ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure {x})
          Subgroup.normalClosure_normal with h | h
        · exact absurd (Subgroup.normalClosure_eq_bot_iff.1 h (Set.mem_singleton x)) hxne
        · exact h
      have hmemH : p i ∈ Subgroup.normalClosure ({x} : Set H) := hne_closure ▸ Subgroup.mem_top _
      have hmemF : q i ∈ Subgroup.normalClosure (insert xFree S) := by
        rw [← hcomap, Subgroup.mem_comap]
        rwa [hq i]
      rw [← hclosure_ext] at hmemF
      exact (mem_normalClosure_iff_exists_cert _ (q i)).1 hmemF
    · intro hcert hxeq
      have hall : ∀ i, p i ∈ Subgroup.normalClosure ({x} : Set H) := by
        intro i
        have : q i ∈ Subgroup.normalClosure
            (Set.range (Fin.snoc relators0 xFree : Fin (r + 1) → FreeGroup (Fin k))) :=
          (mem_normalClosure_iff_exists_cert _ (q i)).2 (hcert i)
        rw [hclosure_ext] at this
        have : π (q i) ∈ Subgroup.normalClosure ({x} : Set H) := by
          rw [← hcomap] at this; exact this
        rwa [hq i] at this
      have htop : Subgroup.normalClosure ({x} : Set H) = ⊤ := by
        apply top_le_iff.1
        rw [← _hp]
        exact Subgroup.closure_le _ |>.2 (fun y ⟨i, hi⟩ => hi ▸ hall i)
      rw [hxeq] at htop
      have hbot : Subgroup.normalClosure ({1} : Set H) = ⊥ :=
        Subgroup.normalClosure_eq_bot_iff.2 (le_refl _)
      rw [hbot] at htop
      exact bot_ne_top htop

  -- Convert the `FreeGroup`-valued certificates to raw-word ones, as in Fact C1.
  have hiff2 : ∀ word : Word n, (∀ i : Fin n, ∃ cert : List (FreeGroup (Fin k) × Bool × Fin (r + 1)),
      q i = certEval (Fin.snoc relators0 (evalWord q word)) cert) ↔
      ∀ i : Fin n, ∃ cert : List (List (Fin k × Bool) × Bool × Fin (r + 1)),
        FreeGroup.mk (qWord i) =
          FreeGroup.mk (rawCertEval (Fin.snoc relWord0 (rawEval qWord word)) cert) := by
    intro word
    have hrelWordExt : ∀ j : Fin (r + 1), FreeGroup.mk ((Fin.snoc relWord0
        (rawEval qWord word) : Fin (r + 1) → List (Fin k × Bool)) j) =
        (Fin.snoc relators0 (evalWord q word) : Fin (r + 1) → FreeGroup (Fin k)) j := by
      intro j
      rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
      · simpa [Fin.snoc_castSucc] using hrelWord0 i
      · simpa [Fin.snoc_last] using (mk_rawEval qWord word).trans
          (congrArg (fun f => evalWord f word) (funext hqWord))
    have hcert_simp : ∀ (cert : List (FreeGroup (Fin k) × Bool × Fin (r + 1))),
        cert.map (fun t => (FreeGroup.mk t.1.toWord, t.2.1, t.2.2)) = cert := by
      intro cert
      conv_rhs => rw [← List.map_id cert]
      apply List.map_congr_left
      intro t _
      simp [FreeGroup.mk_toWord]
    constructor
    · intro h i
      obtain ⟨cert, hcert⟩ := h i
      refine ⟨cert.map (fun t => (FreeGroup.toWord t.1, t.2.1, t.2.2)), ?_⟩
      rw [mk_rawCertEval, List.map_map]
      rw [show ((fun t => (FreeGroup.mk t.1, t.2.1, t.2.2)) ∘
          (fun t : FreeGroup (Fin k) × Bool × Fin (r + 1) => (t.1.toWord, t.2.1, t.2.2))) =
          (fun t => (FreeGroup.mk t.1.toWord, t.2.1, t.2.2)) from rfl]
      rw [hcert_simp cert, hqWord i, show (fun j => FreeGroup.mk ((Fin.snoc relWord0
          (rawEval qWord word) : Fin (r + 1) → List (Fin k × Bool)) j)) =
          Fin.snoc relators0 (evalWord q word) from funext hrelWordExt]
      exact hcert
    · intro h i
      obtain ⟨cert, hcert⟩ := h i
      refine ⟨cert.map (fun t => (FreeGroup.mk t.1, t.2.1, t.2.2)), ?_⟩
      rw [mk_rawCertEval, hqWord i, show (fun j => FreeGroup.mk ((Fin.snoc relWord0
          (rawEval qWord word) : Fin (r + 1) → List (Fin k × Bool)) j)) =
          Fin.snoc relators0 (evalWord q word) from funext hrelWordExt] at hcert
      exact hcert
  -- Skolemize the finite conjunction of existentials into one existential over a list of certs.
  have hiff3 : ∀ word : Word n, (∀ i : Fin n, ∃ cert : List (List (Fin k × Bool) × Bool × Fin (r + 1)),
      FreeGroup.mk (qWord i) = FreeGroup.mk (rawCertEval
        (Fin.snoc relWord0 (rawEval qWord word)) cert)) ↔
      ∃ combined : List (List (List (Fin k × Bool) × Bool × Fin (r + 1))),
        ∀ i : Fin n, FreeGroup.mk (qWord i) = FreeGroup.mk (rawCertEval
          (Fin.snoc relWord0 (rawEval qWord word))
          (combined.getD i.val [])) := by
    intro word
    constructor
    · intro h
      choose f hf using h
      refine ⟨List.ofFn f, fun i => ?_⟩
      have hlen : (List.ofFn f).length = n := List.length_ofFn
      rw [List.getD_eq_getElem?_getD]
      have : (List.ofFn f)[i.val]? = some (f i) := by
        simp
      rw [this]
      exact hf i
    · rintro ⟨combined, hcombined⟩ i
      exact ⟨combined.getD i.val [], hcombined i⟩


  have hre : ∀ (w1 w2 : List (Fin k × Bool)),
      FreeGroup.mk w1 = FreeGroup.mk w2 ↔ FreeGroup.reduce w1 = FreeGroup.reduce w2 :=
    fun w1 w2 => ⟨FreeGroup.reduce.sound, FreeGroup.reduce.exact⟩
  rw [show (fun word : Word n => evalWord p word ≠ 1) =
      (fun word => ∃ combined : List (List (List (Fin k × Bool) × Bool × Fin (r + 1))),
        ∀ i : Fin n, FreeGroup.mk (qWord i) = FreeGroup.mk (rawCertEval
          (Fin.snoc relWord0 (rawEval qWord word) : Fin (r + 1) → List (Fin k × Bool))
          (combined.getD i.val []))) from
    funext (fun word => propext ((hiff word).trans ((hiff2 word).trans (hiff3 word))))]
  set relWord0List : List (List (Fin k × Bool)) := List.ofFn relWord0 with hrelWord0List_def
  -- a plain `ℕ`-indexed lookup, matching `Fin.snoc relWord0 (rawEval qWord word)` pointwise.
  set relWordExtFn : Word n → ℕ → List (Fin k × Bool) :=
    fun word j => if j < r then relWord0List.getD j [] else rawEval qWord word with
    hrelWordExtFn_def
  have hsnoc_eq : ∀ (word : Word n) (j : Fin (r + 1)),
      (Fin.snoc relWord0 (rawEval qWord word) : Fin (r + 1) → List (Fin k × Bool)) j =
        relWordExtFn word (j : ℕ) := by
    intro word j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · have hlt : ((Fin.castSucc i : Fin (r + 1)) : ℕ) < r := i.2
      simp only [hrelWordExtFn_def, hlt, if_true, Fin.snoc_castSucc]
      simp [hrelWord0List_def, List.getD_eq_getElem?_getD]
    · have hnlt : ¬ ((Fin.last r : Fin (r + 1)) : ℕ) < r := by simp
      simp [hrelWordExtFn_def, Fin.snoc_last]
  have hrawEval_primrec : Primrec (fun word : Word n => rawEval qWord word) := by
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
    exact Primrec.list_flatten.comp hmap_primrec
  have hrelWordExtFn_primrec : Primrec₂ relWordExtFn := by
    have hcond : PrimrecPred (fun p : Word n × ℕ => p.2 < r) :=
      Primrec.nat_lt.comp Primrec.snd (Primrec.const r)
    have hleft : Primrec (fun p : Word n × ℕ => relWord0List.getD p.2 []) :=
      (Primrec.list_getD ([] : List (Fin k × Bool))).comp (Primrec.const relWord0List) Primrec.snd
    have hright : Primrec (fun p : Word n × ℕ => rawEval qWord p.1) :=
      hrawEval_primrec.comp Primrec.fst
    exact Primrec.ite hcond hleft hright
  -- the raw-word certificate evaluator over the extended table, as a function of `(word, cert)`.
  have hinvRev_primrec : Primrec (fun w : List (Fin k × Bool) => FreeGroup.invRev w) := by
    have hflip_primrec : Primrec (fun l : Fin k × Bool => (l.1, !l.2)) :=
      Primrec.pair Primrec.fst (Primrec.not.comp Primrec.snd)
    show Primrec (fun w : List (Fin k × Bool) => (w.map (fun l => (l.1, !l.2))).reverse)
    exact Primrec.list_reverse.comp (Primrec.list_map Primrec.id (hflip_primrec.comp Primrec.snd))
  have hrelLookup : Primrec (fun pr : (Word n × List (List (Fin k × Bool) × Bool × Fin (r + 1))) ×
      (List (Fin k × Bool) × Bool × Fin (r + 1)) =>
      relWordExtFn pr.1.1 (pr.2.2.2 : ℕ)) :=
    hrelWordExtFn_primrec.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fin_val.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hcond_sign : PrimrecPred (fun pr : (Word n × List (List (Fin k × Bool) × Bool ×
      Fin (r + 1))) × (List (Fin k × Bool) × Bool × Fin (r + 1)) => pr.2.2.1 = true) :=
    Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const true)
  have hmid : Primrec (fun pr : (Word n × List (List (Fin k × Bool) × Bool × Fin (r + 1))) ×
      (List (Fin k × Bool) × Bool × Fin (r + 1)) =>
      if pr.2.2.1 then relWordExtFn pr.1.1 (pr.2.2.2 : ℕ)
        else FreeGroup.invRev (relWordExtFn pr.1.1 (pr.2.2.2 : ℕ))) :=
    Primrec.ite hcond_sign hrelLookup (hinvRev_primrec.comp hrelLookup)
  have htriple : Primrec (fun pr : (Word n × List (List (Fin k × Bool) × Bool × Fin (r + 1))) ×
      (List (Fin k × Bool) × Bool × Fin (r + 1)) =>
      pr.2.1 ++ (if pr.2.2.1 then relWordExtFn pr.1.1 (pr.2.2.2 : ℕ)
        else FreeGroup.invRev (relWordExtFn pr.1.1 (pr.2.2.2 : ℕ))) ++ FreeGroup.invRev pr.2.1) :=
    Primrec.list_append.comp
      (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd) hmid)
      (hinvRev_primrec.comp (Primrec.fst.comp Primrec.snd))
  have hmap : Primrec (fun pr : Word n × List (List (Fin k × Bool) × Bool × Fin (r + 1)) =>
      pr.2.map (fun t => t.1 ++ (if t.2.1 then relWordExtFn pr.1 (t.2.2 : ℕ)
        else FreeGroup.invRev (relWordExtFn pr.1 (t.2.2 : ℕ))) ++ FreeGroup.invRev t.1)) :=
    Primrec.list_map Primrec.snd (htriple.comp Primrec.id)
  have hrawCertEvalExt_primrec : Primrec (fun pr : Word n ×
      List (List (Fin k × Bool) × Bool × Fin (r + 1)) =>
      rawCertEval (Fin.snoc relWord0 (rawEval qWord pr.1) :
        Fin (r + 1) → List (Fin k × Bool)) pr.2) := by
    refine (Primrec.list_flatten.comp hmap).of_eq (fun pr => ?_)
    simp only [rawCertEval]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [hsnoc_eq]
  have hqWordReduce_primrec : Primrec (fun i : Fin n => FreeGroup.reduce (qWord i)) :=
    primrec_reduce.comp (Primrec.fin_app.comp (Primrec.const qWord) Primrec.id)
  have hcombinedGet : Primrec (fun pr : (Word n ×
      List (List (List (Fin k × Bool) × Bool × Fin (r + 1)))) × Fin n =>
      pr.1.2.getD (pr.2 : ℕ) ([] : List (List (Fin k × Bool) × Bool × Fin (r + 1)))) :=
    (Primrec.list_getD ([] : List (List (Fin k × Bool) × Bool × Fin (r + 1)))).comp
      (Primrec.snd.comp Primrec.fst) (Primrec.fin_val.comp Primrec.snd)
  have hcertEvalExt_perI : Primrec (fun pr : (Word n ×
      List (List (List (Fin k × Bool) × Bool × Fin (r + 1)))) × Fin n =>
      rawCertEval (Fin.snoc relWord0 (rawEval qWord pr.1.1) :
        Fin (r + 1) → List (Fin k × Bool)) (pr.1.2.getD (pr.2 : ℕ) [])) :=
    hrawCertEvalExt_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) hcombinedGet)
  have hperI_decide : Primrec (fun pr : (Word n ×
      List (List (List (Fin k × Bool) × Bool × Fin (r + 1)))) × Fin n =>
      decide (FreeGroup.reduce (qWord pr.2) = FreeGroup.reduce (rawCertEval
        (Fin.snoc relWord0 (rawEval qWord pr.1.1) : Fin (r + 1) → List (Fin k × Bool))
        (pr.1.2.getD (pr.2 : ℕ) [])))) :=
    (Primrec.eq.comp (hqWordReduce_primrec.comp Primrec.snd)
      (primrec_reduce.comp hcertEvalExt_perI)).decide
  have hand_primrec : Primrec (fun bs : List Bool => bs.foldr Bool.and true) :=
    Primrec.list_foldr (f := @id (List Bool)) (g := fun _ : List Bool => true)
      (h := fun (_ : List Bool) (q : Bool × Bool) => Bool.and q.1 q.2)
      Primrec.id (Primrec.const true)
      ((Primrec.and.comp Primrec.fst Primrec.snd).comp Primrec.snd)
  have hall_primrec : Primrec (fun pr : Word n ×
      List (List (List (Fin k × Bool) × Bool × Fin (r + 1))) =>
      ((List.finRange n).map (fun i => decide (FreeGroup.reduce (qWord i) =
        FreeGroup.reduce (rawCertEval (Fin.snoc relWord0 (rawEval qWord pr.1) :
          Fin (r + 1) → List (Fin k × Bool)) (pr.2.getD (i : ℕ) []))))).foldr Bool.and true) := by
    have hmapped : Primrec (fun pr : Word n ×
        List (List (List (Fin k × Bool) × Bool × Fin (r + 1))) =>
        (List.finRange n).map (fun i => decide (FreeGroup.reduce (qWord i) =
          FreeGroup.reduce (rawCertEval (Fin.snoc relWord0 (rawEval qWord pr.1) :
            Fin (r + 1) → List (Fin k × Bool)) (pr.2.getD (i : ℕ) []))))) :=
      Primrec.list_map (Primrec.const (List.finRange n)) hperI_decide
    exact hand_primrec.comp hmapped
  have hall_eq : ∀ (bs : List Bool), bs.foldr Bool.and true = bs.all id := by
    intro bs
    induction bs with
    | nil => rfl
    | cons b bs ih => simp [ih, List.all_cons, Bool.and, id]
  have hcomp : Computable (fun pr : Word n ×
      List (List (List (Fin k × Bool) × Bool × Fin (r + 1))) =>
      decide (∀ i : Fin n, FreeGroup.mk (qWord i) = FreeGroup.mk (rawCertEval
        (Fin.snoc relWord0 (rawEval qWord pr.1) : Fin (r + 1) → List (Fin k × Bool))
        (pr.2.getD i.val [])))) :=
    hall_primrec.to_comp.of_eq (fun pr => by
      rw [hall_eq, List.all_map]
      have key : (List.finRange n).all (id ∘ fun i => decide (FreeGroup.reduce (qWord i) =
          FreeGroup.reduce (rawCertEval (Fin.snoc relWord0 (rawEval qWord pr.1) :
            Fin (r + 1) → List (Fin k × Bool)) (pr.2.getD (i : ℕ) [])))) = true ↔
          ∀ i : Fin n, FreeGroup.mk (qWord i) = FreeGroup.mk (rawCertEval
            (Fin.snoc relWord0 (rawEval qWord pr.1) : Fin (r + 1) → List (Fin k × Bool))
            (pr.2.getD i.val [])) := by
        rw [List.all_eq_true]
        constructor
        · intro h i
          have := h i (List.mem_finRange i)
          simp only [Function.comp_apply, id_eq, decide_eq_true_eq] at this
          rwa [hre]
        · intro h i _
          simp only [Function.comp_apply, id_eq, decide_eq_true_eq]
          rw [← hre]
          exact h i
      by_cases hb : (List.finRange n).all (id ∘ fun i => decide (FreeGroup.reduce (qWord i) =
          FreeGroup.reduce (rawCertEval (Fin.snoc relWord0 (rawEval qWord pr.1) :
            Fin (r + 1) → List (Fin k × Bool)) (pr.2.getD (i : ℕ) [])))) = true
      · rw [hb]
        symm
        rw [decide_eq_true_eq]
        exact key.1 hb
      · rw [Bool.not_eq_true] at hb
        rw [hb]
        symm
        rw [decide_eq_false_iff_not]
        intro hcon
        rw [key.2 hcon] at hb
        exact absurd hb (by decide))
  refine (REPred.of_exists (γ := Word n) (β := ℕ)
      (R := fun (word : Word n) (nIdx : ℕ) =>
        Option.elim (Encodable.decode nIdx :
            Option (List (List (List (Fin k × Bool) × Bool × Fin (r + 1))))) False
          (fun combined => ∀ i : Fin n, FreeGroup.mk (qWord i) = FreeGroup.mk (rawCertEval
            (Fin.snoc relWord0 (rawEval qWord word) : Fin (r + 1) → List (Fin k × Bool))
            (combined.getD i.val []))))
      ?_).of_eq (fun word => by
    constructor
    · rintro ⟨nIdx, hnIdx⟩
      rcases hd : (Encodable.decode nIdx :
          Option (List (List (List (Fin k × Bool) × Bool × Fin (r + 1))))) with _ | combined
      · rw [hd] at hnIdx; exact absurd hnIdx id
      · rw [hd] at hnIdx; exact ⟨combined, hnIdx⟩
    · rintro ⟨combined, hcombined⟩
      refine ⟨Encodable.encode combined, ?_⟩
      rw [Encodable.encodek]
      exact hcombined)
  refine ⟨fun pr => by classical infer_instance, ?_⟩
  have hfinal := computable_option_elim_decide
    (P := fun (word : Word n) (combined : List (List (List (Fin k × Bool) × Bool × Fin (r + 1)))) =>
      ∀ i : Fin n, FreeGroup.mk (qWord i) = FreeGroup.mk (rawCertEval
        (Fin.snoc relWord0 (rawEval qWord word) : Fin (r + 1) → List (Fin k × Bool))
        (combined.getD i.val [])))
    hcomp
  exact hfinal.of_eq (fun pr => by
    rcases h : (Encodable.decode pr.2 :
        Option (List (List (List (Fin k × Bool) × Bool × Fin (r + 1))))) with _ | combined <;>
      simp [h])

