-- Prove2me | solution 1 for ObfImpossibility.RiceNoSize.finite_queries
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T13:28:21.207905+00:00
-- url     : https://prove2.me/submissions/dec4e302-104f-4134-9aec-774b86c14bf7

import Mathlib
import Definitions.Def_ObfImpossibility_RiceNoSize_ProofObjects
/-
Finite-use principle in Barak et al., On the (Im)possibility of Obfuscating Programs,
J. ACM 59(2), author's copy, proof of Theorem A.4, p. A:42.
Reuses tomasz's actual accepted bounded-evaluation soundness/completeness proof:
target 53930add-5669-4982-ac98-9cb7cde44ab7,
submission 8ad099b2-5e8b-4320-87ce-c5b02e625199,
original SHA256 476fd5e7e0bb3e7544b9f24ef89469d1ad0bbd8c6ca491f1ad1ef64b361de42b.
Only its final declaration is renamed to oracle_adequacy.
OpenAI Codex supplied bounded-evaluation locality and the finite-query specialization
for Alexander Richard Towell's campaign; no novelty or human review claimed.
-/

set_option autoImplicit false

open FriedbergMuchnik

/-- A successful sequential search records zero at its answer and defined
nonzero values at every earlier candidate. -/
private theorem boundedMu_sound {f : ℕ → Option ℕ} {k n y : ℕ}
    (h : boundedMu f k n = some y) :
    n ≤ y ∧ f y = some 0 ∧
      ∀ m, n ≤ m → m < y → ∃ v, f m = some v ∧ v ≠ 0 := by
  induction k generalizing n with
  | zero => simp [boundedMu] at h
  | succ k ih =>
      change (f n).bind (fun v => if v = 0 then some n else boundedMu f k (n + 1)) = some y at h
      obtain ⟨v, hv, hy⟩ := Option.bind_eq_some_iff.mp h
      by_cases hz : v = 0
      · simp only [hz, ↓reduceIte, Option.some.injEq] at hy
        subst y
        exact ⟨le_refl _, hz ▸ hv, by intros; omega⟩
      · simp only [hz, ↓reduceIte] at hy
        obtain ⟨hny, hfy, hbefore⟩ := ih hy
        refine ⟨by omega, hfy, ?_⟩
        intro m hnm hmy
        by_cases heq : m = n
        · exact ⟨v, by simpa [heq] using hv, hz⟩
        · exact hbefore m (by omega) hmy

/-- A finite sequence of defined nonzero tests followed by zero is found
whenever the supplied search interval includes that candidate. -/
private theorem boundedMu_complete {f : ℕ → Option ℕ} {k n y : ℕ}
    (hny : n ≤ y) (hyk : y < n + k) (hy : f y = some 0)
    (hbefore : ∀ m, n ≤ m → m < y → ∃ v, f m = some v ∧ v ≠ 0) :
    boundedMu f k n = some y := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
      by_cases heq : n = y
      · simp [boundedMu, heq, hy]
      · obtain ⟨v, hv, hv0⟩ := hbefore n (le_refl n) (by omega)
        change (f n).bind (fun v => if v = 0 then some n else boundedMu f k (n + 1)) = some y
        rw [hv]
        simp only [Option.bind_some, hv0, ↓reduceIte]
        exact ih (n := n + 1) (by omega) (by omega) (fun m hm => hbefore m (by omega))

/-- Every successful finite simulation is valid in the partial semantics. -/
private theorem evaln_sound (O : ℕ → ℕ) (c : Program) (k x y : ℕ)
    (h : oracleEvaln O k c x = some y) :
    y ∈ oracleEval (PFun.lift O) c x := by
  induction k generalizing c x y with
  | zero => simp [oracleEvaln] at h
  | succ k ih =>
      have hx : x < k + 1 := by
        by_contra hn
        simp [oracleEvaln, hn] at h
      cases c with
      | query => simpa [oracleEvaln, oracleEval, hx, eq_comm] using h
      | succ => simpa [oracleEvaln, oracleEval, hx, eq_comm] using h
      | left => simpa [oracleEvaln, oracleEval, hx, eq_comm] using h
      | right => simpa [oracleEvaln, oracleEval, hx, eq_comm] using h
      | pair f g =>
          simp only [oracleEvaln, hx, ↓reduceIte] at h
          obtain ⟨a, ha, hrest⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨b, hgb, hab⟩ := Option.bind_eq_some_iff.mp hrest
          have hab : Nat.pair a b = y := Option.some.inj hab
          subst y
          simp only [oracleEval, Seq.seq, Part.map_eq_map, Part.mem_bind_iff, Part.mem_map_iff]
          exact ⟨Nat.pair a, ⟨a, ih f x a ha, rfl⟩, b, ih g x b hgb, rfl⟩
      | comp f g =>
          simp only [oracleEvaln, hx, ↓reduceIte] at h
          obtain ⟨a, ha, hy⟩ := Option.bind_eq_some_iff.mp h
          exact Part.mem_bind_iff.mpr ⟨a, ih g x a ha, ih f a y hy⟩
      | prec f g =>
          simp only [oracleEvaln, hx, ↓reduceIte] at h
          simp only [oracleEval]
          have hrec : ∀ m v : ℕ,
              (m.rec (oracleEvaln O k f x.unpair.1) fun j ih =>
                ih.bind fun z => oracleEvaln O k g (Nat.pair x.unpair.1 (Nat.pair j z))) = some v →
              v ∈ (m.rec (oracleEval (PFun.lift O) f x.unpair.1) (fun j ih =>
                ih.bind fun z => oracleEval (PFun.lift O) g (Nat.pair x.unpair.1 (Nat.pair j z))) : Part ℕ) := by
            intro m
            induction m with
            | zero => exact ih f x.unpair.1
            | succ m ihm =>
                intro v hv
                obtain ⟨z, hz, hv⟩ := Option.bind_eq_some_iff.mp hv
                exact Part.mem_bind_iff.mpr ⟨z, ihm z hz, ih g _ v hv⟩
          exact hrec x.unpair.2 y h
      | mu f =>
          simp only [oracleEvaln, hx, ↓reduceIte] at h
          obtain ⟨_, hy, hbefore⟩ := boundedMu_sound h
          apply Nat.mem_rfind.mpr
          constructor
          · exact (Part.mem_map_iff _).mpr ⟨0, ih f _ 0 hy, by simp⟩
          · intro m hm
            obtain ⟨v, hv, hv0⟩ := hbefore m (Nat.zero_le m) hm
            exact (Part.mem_map_iff _).mpr ⟨v, ih f _ v hv, by simpa using hv0⟩

/-- Finitely many eventual bounds have a common bound. -/
private theorem finite_eventual_bound (m : ℕ) (P : ℕ → ℕ → Prop)
    (h : ∀ j, j < m → ∃ k, ∀ r, k ≤ r → P j r) :
    ∃ k, ∀ r, k ≤ r → ∀ j, j < m → P j r := by
  induction m with
  | zero => exact ⟨0, by intros; omega⟩
  | succ m ih =>
      obtain ⟨k₁, hk₁⟩ := ih (fun j hj => h j (by omega))
      obtain ⟨k₂, hk₂⟩ := h m (by omega)
      refine ⟨max k₁ k₂, ?_⟩
      intro r hr j hj
      by_cases hjm : j < m
      · exact hk₁ r (by omega) j hjm
      · have : j = m := by omega
        subst j
        exact hk₂ r (by omega)

/-- A convergent computation succeeds at every sufficiently large fuel. -/
private theorem evaln_complete (O : ℕ → ℕ) (c : Program) (x y : ℕ)
    (h : y ∈ oracleEval (PFun.lift O) c x) :
    ∃ k, ∀ r, k ≤ r → oracleEvaln O r c x = some y := by
  induction c generalizing x y with
  | query =>
      refine ⟨x + 1, ?_⟩
      intro r hr
      cases r with
      | zero => omega
      | succ r => simpa [oracleEval, oracleEvaln, show x < r + 1 by omega, eq_comm] using h
  | succ =>
      refine ⟨x + 1, ?_⟩
      intro r hr
      cases r with
      | zero => omega
      | succ r => simpa [oracleEval, oracleEvaln, show x < r + 1 by omega, eq_comm] using h
  | left =>
      refine ⟨x + 1, ?_⟩
      intro r hr
      cases r with
      | zero => omega
      | succ r => simpa [oracleEval, oracleEvaln, show x < r + 1 by omega, eq_comm] using h
  | right =>
      refine ⟨x + 1, ?_⟩
      intro r hr
      cases r with
      | zero => omega
      | succ r => simpa [oracleEval, oracleEvaln, show x < r + 1 by omega, eq_comm] using h
  | pair f g ihf ihg =>
      simp only [oracleEval, Seq.seq, Part.map_eq_map, Part.mem_bind_iff, Part.mem_map_iff] at h
      obtain ⟨F, ⟨a, ha, hF⟩, b, hb, hout⟩ := h
      subst F
      subst y
      obtain ⟨k₁, hk₁⟩ := ihf x a ha
      obtain ⟨k₂, hk₂⟩ := ihg x b hb
      refine ⟨max x (max k₁ k₂) + 1, ?_⟩
      intro r hr
      cases r with
      | zero => omega
      | succ r =>
          simp [oracleEvaln, show x < r + 1 by omega,
            hk₁ r (by omega), hk₂ r (by omega)]
  | comp f g ihf ihg =>
      obtain ⟨a, ha, hy⟩ := Part.mem_bind_iff.mp h
      obtain ⟨k₁, hk₁⟩ := ihg x a ha
      obtain ⟨k₂, hk₂⟩ := ihf a y hy
      refine ⟨max x (max k₁ k₂) + 1, ?_⟩
      intro r hr
      cases r with
      | zero => omega
      | succ r =>
          simp [oracleEvaln, show x < r + 1 by omega,
            hk₁ r (by omega), hk₂ r (by omega)]
  | prec f g ihf ihg =>
      have hrec : ∀ m v : ℕ,
          v ∈ (m.rec (oracleEval (PFun.lift O) f x.unpair.1) (fun j ih =>
            ih.bind fun z => oracleEval (PFun.lift O) g (Nat.pair x.unpair.1 (Nat.pair j z))) : Part ℕ) →
          ∃ k, ∀ r, k ≤ r →
            (m.rec (oracleEvaln O r f x.unpair.1) fun j ih =>
              ih.bind fun z => oracleEvaln O r g (Nat.pair x.unpair.1 (Nat.pair j z))) = some v := by
        intro m
        induction m with
        | zero => exact ihf x.unpair.1
        | succ m ihm =>
            intro v hv
            obtain ⟨z, hz, hv⟩ := Part.mem_bind_iff.mp hv
            obtain ⟨k₁, hk₁⟩ := ihm z hz
            obtain ⟨k₂, hk₂⟩ := ihg (Nat.pair x.unpair.1 (Nat.pair m z)) v hv
            refine ⟨max k₁ k₂, ?_⟩
            intro r hr
            change (m.rec (oracleEvaln O r f x.unpair.1) (fun j ih =>
              ih.bind fun z => oracleEvaln O r g (Nat.pair x.unpair.1 (Nat.pair j z))) : Option ℕ).bind _ = some v
            rw [hk₁ r (by omega), Option.bind_some]
            exact hk₂ r (by omega)
      obtain ⟨k, hk⟩ := hrec x.unpair.2 y h
      refine ⟨max x k + 1, ?_⟩
      intro r hr
      cases r with
      | zero => omega
      | succ r =>
          simp only [oracleEvaln, show x < r + 1 by omega, ↓reduceIte]
          exact hk r (by omega)
  | mu f ih =>
      have hmin := Nat.mem_rfind.mp h
      have hy : 0 ∈ oracleEval (PFun.lift O) f (Nat.pair x y) := by
        simpa using hmin.1
      have hbefore : ∀ j, j < y →
          ∃ v, v ∈ oracleEval (PFun.lift O) f (Nat.pair x j) ∧ v ≠ 0 := by
        intro j hj
        simpa using hmin.2 hj
      have hpoints : ∀ j, j < y + 1 → ∃ k, ∀ r, k ≤ r →
          (j = y → oracleEvaln O r f (Nat.pair x j) = some 0) ∧
          (j < y → ∃ v, oracleEvaln O r f (Nat.pair x j) = some v ∧ v ≠ 0) := by
        intro j hj
        by_cases heq : j = y
        · subst j
          obtain ⟨k, hk⟩ := ih (Nat.pair x y) 0 hy
          exact ⟨k, fun r hr => ⟨fun _ => hk r hr, by intros; omega⟩⟩
        · obtain ⟨v, hv, hv0⟩ := hbefore j (by omega)
          obtain ⟨k, hk⟩ := ih (Nat.pair x j) v hv
          exact ⟨k, fun r hr => ⟨fun h => (heq h).elim, fun _ => ⟨v, hk r hr, hv0⟩⟩⟩
      obtain ⟨k, hk⟩ := finite_eventual_bound (y + 1) _ hpoints
      refine ⟨max k (max x y) + 1, ?_⟩
      intro r hr
      cases r with
      | zero => omega
      | succ r =>
          simp only [oracleEvaln, show x < r + 1 by omega, ↓reduceIte]
          apply boundedMu_complete (n := 0) (Nat.zero_le y) (by omega)
          · exact (hk r (by omega) y (by omega)).1 rfl
          · intro j _ hj
            exact (hk r (by omega) j (by omega)).2 hj

theorem oracle_adequacy (O : ℕ → ℕ) (c : Program) (x y : ℕ) :
    y ∈ oracleEval (PFun.lift O) c x ↔
      ∃ k : ℕ, oracleEvaln O k c x = some y := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := evaln_complete O c x y h
    exact ⟨k, hk k (le_refl k)⟩
  · rintro ⟨k, hk⟩
    exact evaln_sound O c k x y hk


open FriedbergMuchnik

namespace OracleUse

theorem evaln_local (k : ℕ) (O O' : ℕ → ℕ) (hO : ∀ q, q < k → O q = O' q)
    (c : Program) (x : ℕ) : oracleEvaln O k c x = oracleEvaln O' k c x := by
  induction k generalizing c x with
  | zero => rfl
  | succ k ih =>
    have he : oracleEvaln O k = oracleEvaln O' k := by
      funext d y
      exact ih (fun q hq => hO q (by omega)) d y
    cases c <;> simp only [oracleEvaln, he]
    split_ifs with hx
    · rw [hO x hx]
    · rfl

end OracleUse

open ObfImpossibility.RiceNoSize

theorem solution (S : FriedbergMuchnik.Program) (M₀ : Machine) (σ : ℕ)
    (h : simRun S M₀ = Part.some σ) :
    ∃ n : ℕ, ∀ M : Machine,
      (∀ t x : ℕ, t ≤ n → x ≤ n → bounded M t x = bounded M₀ t x) →
      simRun S M = Part.some σ := by
  have hm : σ ∈ oracleEval (PFun.lift (oracle M₀)) S 0 := by
    change σ ∈ simRun S M₀
    simp [h]
  obtain ⟨k,hk⟩ := (oracle_adequacy (oracle M₀) S 0 σ).mp hm
  refine ⟨k,?_⟩
  intro M hM
  have horacle : ∀ q, q < k → oracle M q = oracle M₀ q := by
    intro q hq
    unfold oracle
    rw [hM q.unpair.1 q.unpair.2
      ((Nat.unpair_left_le q).trans (by omega))
      ((Nat.unpair_right_le q).trans (by omega))]
  have he := OracleUse.evaln_local k (oracle M) (oracle M₀) horacle S 0
  have hv : σ ∈ simRun S M :=
    (oracle_adequacy (oracle M) S 0 σ).mpr ⟨k,he.trans hk⟩
  exact Part.eq_some_iff.mpr hv

#print axioms solution
