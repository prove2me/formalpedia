-- Prove2me | solution 1 for TimeSpaceMA.constantLossFlatExtractor
-- status  : ACCEPTED   (prove)
-- author  : @bersubs
-- created : 2026-11-14T20:12:01.125282+00:00
-- url     : https://prove2.me/submissions/88325b6c-f634-41ea-a08c-fe190dc7d580

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryDiv
import Definitions.Def_TimeSpaceMA_TUZExtractor
import Definitions.Def_TimeSpaceMA_TUZExtractorComponents
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_TimeSpaceMA_shortLosslessCondenser
import Theorems.Thm_TimeSpaceMA_polylogConstantLossExtractor

namespace TimeSpaceMA

section
variable {Input Seed Extra Out : Type} [Fintype Seed] [Fintype Extra] [Fintype Out]
variable [DecidableEq Extra] [DecidableEq Out]

/-- A weak extractor can carry additional independent seed bits directly to the output,
without changing its statistical error. -/
theorem FlatExtractorEvents.withIndependentSeed
    (E : Input → Seed → Out) (S : Finset Input) (ε : ℝ)
    (hExtra : 0 < Fintype.card Extra) (hE : FlatExtractorEvents E S ε) :
    FlatExtractorEvents (fun x (z : Seed × Extra) => (E x z.1,z.2)) S ε := by
  classical
  intro A
  let T := fun t : Extra => Finset.univ.filter (fun y : Out => (y,t) ∈ A)
  let F := fun t : Extra => (S ×ˢ Finset.univ).filter (fun q : Input × Seed => E q.1 q.2 ∈ T t)
  let G := (S ×ˢ Finset.univ).filter (fun q : Input × (Seed × Extra) => (E q.1 q.2.1,q.2.2) ∈ A)
  have hT (y : Out) (t : Extra) : y ∈ T t ↔ (y,t) ∈ A := by simp [T]
  have hcountG : G.card = ∑ t : Extra, (F t).card := by
    rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
    simp only [Finset.sum_product]
    conv_rhs => enter [2, t]; rw [Finset.card_filter, Finset.sum_product]
    simp only [hT]
    trans ∑ x ∈ S, ∑ t : Extra, ∑ u : Seed, if (E x u, t) ∈ A then 1 else 0
    · apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    · rw [Finset.sum_comm]
  have hcountA : A.card = ∑ t : Extra, (T t).card := by
    have hsum := Finset.card_eq_sum_card_fiberwise (f := Prod.snd)
      (t := (Finset.univ : Finset Extra)) (s := A) (fun _ _ => Finset.mem_univ _)
    rw [hsum]
    apply Finset.sum_congr rfl
    intro t _
    symm
    have heq : (A.filter fun p : Out × Extra => p.2 = t) =
        (T t).map ⟨fun y => (y,t), fun a b h => (congrArg Prod.fst h : a = b)⟩ := by
      ext x
      obtain ⟨y,u⟩ := x
      constructor
      · intro hx
        obtain ⟨hya,hu⟩ := Finset.mem_filter.mp hx
        change u = t at hu
        subst u
        exact Finset.mem_map.mpr ⟨y,(hT y t).mpr hya,rfl⟩
      · intro hx
        obtain ⟨z,hz,he⟩ := Finset.mem_map.mp hx
        change (z,t) = (y,u) at he
        cases he
        exact Finset.mem_filter.mpr ⟨(hT _ _).mp hz,rfl⟩
    rw [heq, Finset.card_map]
  have hrealG : (G.card : ℝ) = ∑ t : Extra, ((F t).card : ℝ) := by exact_mod_cast hcountG
  have hrealA : (A.card : ℝ) = ∑ t : Extra, ((T t).card : ℝ) := by exact_mod_cast hcountA
  let a : ℝ := S.card
  let d : ℝ := Fintype.card Seed
  let q : ℝ := Fintype.card Extra
  let r : ℝ := Fintype.card Out
  have hq : 0 < q := by dsimp [q]; exact_mod_cast hExtra
  have heach (t : Extra) : ((F t).card : ℝ) / (a*d) - ((T t).card : ℝ) / r ≤ ε := hE (T t)
  have hsum : ∑ t : Extra, (((F t).card : ℝ) / (a*d) - ((T t).card : ℝ) / r) ≤ q*ε := by
    calc
      _ ≤ ∑ _t : Extra, ε := Finset.sum_le_sum (fun t _ => heach t)
      _ = _ := by simp [nsmul_eq_mul, q]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, ← hrealG, ← hrealA] at hsum
  change (G.card : ℝ) / ((S.card : ℝ) * (Fintype.card (Seed × Extra) : ℝ)) -
      (A.card : ℝ) / (Fintype.card (Out × Extra) : ℝ) ≤ ε
  simp only [Fintype.card_prod, Nat.cast_mul]
  change (G.card : ℝ) / (a*(d*q)) - (A.card : ℝ) / (r*q) ≤ ε
  rw [← mul_assoc, ← div_div _ (a*d) q, ← div_div _ r q, ← sub_div]
  exact (div_le_iff₀ hq).mpr (by simpa [mul_comm] using hsum)

end

section Relabel
variable {Input Seed Seed' Out Out' : Type} [Fintype Seed] [Fintype Seed'] [Fintype Out] [Fintype Out']
variable [DecidableEq Out] [DecidableEq Out']

/-- Relabel seeds and outputs by arbitrary bijections without changing the extractor error. -/
theorem FlatExtractorEvents.equivSeedOutput
    (E : Input → Seed → Out) (S : Finset Input) (ε : ℝ)
    (eS : Seed' ≃ Seed) (eO : Out ≃ Out') (hE : FlatExtractorEvents E S ε) :
    FlatExtractorEvents (fun x t => eO (E x (eS t))) S ε := by
  classical
  intro A
  let B := A.map eO.symm.toEmbedding
  let f : (Input × Seed') ↪ (Input × Seed) := (Equiv.prodCongr (Equiv.refl Input) eS).toEmbedding
  let X := (S ×ˢ Finset.univ).filter (fun p : Input × Seed' => eO (E p.1 (eS p.2)) ∈ A)
  let Y := (S ×ˢ Finset.univ).filter (fun p : Input × Seed => E p.1 p.2 ∈ B)
  have hB (y : Out) : y ∈ B ↔ eO y ∈ A := by
    change y ∈ A.map eO.symm.toEmbedding ↔ eO y ∈ A
    constructor
    · intro hy
      obtain ⟨u,hu,he⟩ := Finset.mem_map.mp hy
      change eO.symm u = y at he
      simpa [← he] using hu
    · intro h
      exact Finset.mem_map.mpr ⟨_,h,eO.symm_apply_apply y⟩
  have hXY : X.map f = Y := by
    ext p
    obtain ⟨x,t⟩ := p
    constructor
    · intro hp
      obtain ⟨⟨u,s⟩,hu,he⟩ := Finset.mem_map.mp hp
      change (u,eS s) = (x,t) at he
      cases he
      obtain ⟨hm,hy⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp hm).1,
        Finset.mem_univ _⟩,(hB _).2 hy⟩
    · intro hp
      obtain ⟨hm,hy⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_map.mpr ⟨(x,eS.symm t),Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp hm).1,Finset.mem_univ _⟩,?_⟩,?_⟩
      · simpa using (hB _).1 hy
      · change (x,eS (eS.symm t)) = (x,t)
        rw [eS.apply_symm_apply]
  have hcard : X.card = Y.card := by rw [← hXY, Finset.card_map]
  change (X.card : ℝ) / ((S.card : ℝ) * (Fintype.card Seed' : ℝ)) -
    (A.card : ℝ) / (Fintype.card Out' : ℝ) ≤ ε
  rw [hcard, Fintype.card_congr eS, ← Fintype.card_congr eO]
  have h := hE B
  change (Y.card : ℝ) / ((S.card : ℝ) * (Fintype.card Seed : ℝ)) -
    (B.card : ℝ) / (Fintype.card Out : ℝ) ≤ ε at h
  simpa [B] using h

end Relabel

/-- Decode a padded seed into the original seed and independently appended seed. -/
def paddedSeedEquiv (t extra : ℕ) : Fin (2^(t+extra)) ≃ Fin (2^t) × Fin (2^extra) :=
  (finCongr (pow_add 2 t extra)).trans finProdFinEquiv.symm

/-- Encode the original output and the independently appended seed back into one label. -/
def paddedOutputEquiv (m extra : ℕ) : Fin (2^m) × Fin (2^extra) ≃ Fin (2^(m+extra)) :=
  finProdFinEquiv.trans (finCongr (pow_add 2 m extra).symm)

/-- Extending the seed of a binary extractor increases the output width by the same amount.
The extra seed forms the low-order bits of the output. -/
theorem FlatExtractorEvents.padBinarySeed {Input : Type} (t m extra : ℕ)
    (E : Input → Fin (2^t) → Fin (2^m)) (S : Finset Input) (ε : ℝ)
    (hE : FlatExtractorEvents E S ε) :
    FlatExtractorEvents (fun x (s : Fin (2^(t+extra))) =>
      paddedOutputEquiv m extra (E x ((paddedSeedEquiv t extra s).1), (paddedSeedEquiv t extra s).2)) S ε := by
  have hind := FlatExtractorEvents.withIndependentSeed (Extra := Fin (2^extra)) E S ε
    (by simp) hE
  exact FlatExtractorEvents.equivSeedOutput (fun x (z : Fin (2^t) × Fin (2^extra)) => (E x z.1,z.2))
    S ε (paddedSeedEquiv t extra) (paddedOutputEquiv m extra) hind

/-- Changing a seed's finite carrier by an index equality preserves the extractor property. -/
theorem FlatExtractorEvents.comapSeedCast {Input Out : Type} {s t : ℕ}
    [Fintype Out] [DecidableEq Out] {E : Input → Fin t → Out}
    {S : Finset Input} {ε : ℝ} (h : s = t) (hE : FlatExtractorEvents E S ε) :
    FlatExtractorEvents (fun x i => E x (Fin.cast h i)) S ε := by
  exact FlatExtractorEvents.equivSeedOutput E S ε (finCongr h) (Equiv.refl Out) hE

/-- Casting all right vertex indices along equality preserves the cardinal of each neighborhood. -/
theorem finCast_neighbor_card {Input Seed : Type} {r r' : ℕ} [Fintype Seed]
    (h : r = r') (E : Input → Seed → Fin r) (S : Finset Input) :
    (S.biUnion (fun x => Finset.univ.image (fun i => Fin.cast h (E x i)))).card =
      (S.biUnion (fun x => Finset.univ.image (E x))).card := by
  subst r'
  rfl

end TimeSpaceMA

namespace TimeSpaceMA

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Increase an extractor's seed width using independent spare bits. The input
width, entropy target, and seed width retain the same outer encoding. -/
def padExtractor (baseSeed : ℕ × ℕ → ℕ) (base : ExtractorInput → ℕ) (Δ : ℕ) :
    ExtractorInput → ℕ :=
  fun (n,k,t,x,y) =>
    let k := min n k
    let r := baseSeed (n,k)
    let spare := (2 : ℕ)^(t-r)
    (base (n,k,r,x,y/spare) % 2^(k+r-Δ)) * spare + y % spare

private theorem padExtractor_polytime (baseSeed : ℕ × ℕ → ℕ)
    (base : ExtractorInput → ℕ) (Δ : ℕ)
    (hseed : ComputableInPolyTime baseSeed (encPair encUnary encNat) encUnary)
    (hbase : ComputableInPolyTime base encExtractorInput encNat) :
    ComputableInPolyTime (padExtractor baseSeed base Δ) encExtractorInput encNat := by
  apply ComputableTidilyInPolyTime.computableInPolyTime
  let input := encExtractorInput
  let n := fun x : ExtractorInput => x.1
  let kraw := fun x : ExtractorInput => x.2.1
  let k := fun x => min (n x) (kraw x)
  let t := fun x : ExtractorInput => x.2.2.1
  let val := fun x : ExtractorInput => x.2.2.2.1
  let seed := fun x : ExtractorInput => x.2.2.2.2
  have hn : ComputableTidilyInPolyTime n input encUnary := fst _ _
  have hkRaw : ComputableTidilyInPolyTime kraw input encNat := (snd _ _).fst'
  have hku : ComputableTidilyInPolyTime k input encUnary :=
    (ComputableInPolyTime.binary_min_unary' hn.computableInPolyTime hkRaw.computableInPolyTime).tidy
  have hk : ComputableTidilyInPolyTime k input encNat := unary_to_binary.comp hku
  have ht : ComputableTidilyInPolyTime t input encUnary := (snd _ _).snd'.fst'
  have hval : ComputableTidilyInPolyTime val input encNat := (snd _ _).snd'.snd'.fst'
  have hseedIn : ComputableTidilyInPolyTime seed input encNat := (snd _ _).snd'.snd'.snd'
  let r := fun x => baseSeed (n x,k x)
  have hr : ComputableTidilyInPolyTime r input encUnary := hseed.tidy.comp (hn.prod hk)
  let spare := fun x => (2:ℕ)^(t x-r x)
  have hspare : ComputableTidilyInPolyTime spare input encNat :=
    binary_two_pow.comp (unary_sub.comp (ht.prod hr))
  have hw : ComputableTidilyInPolyTime (fun x => (2:ℕ)^(k x+r x-Δ)) input encNat :=
    binary_two_pow.comp (unary_sub.comp ((unary_add.comp (hku.prod hr)).prod (const Δ)))
  exact binary_add' (binary_mul'
      (binary_mod' (hbase.tidy.comp (hn.prod (hk.prod (hr.prod
        (hval.prod (binary_div' hseedIn hspare)))))) hw) hspare)
    (binary_mod' hseedIn hspare)


/-- On valid parameters the arithmetic wrapper appends exactly the extra seed's
uniform low bits, under the canonical product equivalences. -/
theorem FlatExtractorEvents.padExtractor (baseSeed : ℕ × ℕ → ℕ)
    (base : ExtractorInput → ℕ) (Δ n k t : ℕ) (hkn : k ≤ n)
    (hr : baseSeed (n,k) ≤ t) (hΔ : Δ ≤ k + baseSeed (n,k))
    (S : Finset (Fin (2^n))) (ε : ℝ)
    (hbase : FlatExtractorEvents (extractorEdge base Δ n k (baseSeed (n,k))) S ε) :
    FlatExtractorEvents (extractorEdge (TimeSpaceMA.padExtractor baseSeed base Δ) Δ n k t) S ε := by
  let r := baseSeed (n,k)
  let b := t-r
  have htr : r+b = t := by omega
  have hout : (k+r-Δ)+b = k+t-Δ := by omega
  have hpad := FlatExtractorEvents.padBinarySeed r (k+r-Δ) b
    (extractorEdge base Δ n k r) S ε hbase
  let eIn : Fin (2^t) ≃ Fin (2^(r+b)) := finCongr (congrArg (fun z : ℕ => 2^z) htr.symm)
  let eOut : Fin (2^((k+r-Δ)+b)) ≃ Fin (2^(k+t-Δ)) :=
    finCongr (congrArg (fun z : ℕ => 2^z) hout)
  have he := FlatExtractorEvents.equivSeedOutput _ S ε eIn eOut hpad
  convert he using 2
  rename_i x
  funext y
  apply Fin.ext
  have hbound (z : Fin (2^(k+r-Δ)) × Fin (2^b)) :
      z.1.val * 2^b + z.2.val < 2^(k+t-Δ) := by
    rw [← hout, pow_add]
    calc
      _ < z.1.val*2^b+2^b := Nat.add_lt_add_left z.2.isLt _
      _ = (z.1.val+1)*2^b := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt z.1.isLt)
  have hb := hbound
    (extractorEdge base Δ n k r x ((paddedSeedEquiv r b (eIn y)).1),
      (paddedSeedEquiv r b (eIn y)).2)
  let z := (extractorEdge base Δ n k r x ((paddedSeedEquiv r b (eIn y)).1),
    (paddedSeedEquiv r b (eIn y)).2)
  change
    (TimeSpaceMA.padExtractor baseSeed base Δ (n,k,t,x.val,y.val)) % 2^(k+t-Δ) =
      z.2.val + 2^b * z.1.val
  have hraw : TimeSpaceMA.padExtractor baseSeed base Δ (n,k,t,x.val,y.val) =
      z.1.val * 2^b + z.2.val := by
    simp only [TimeSpaceMA.padExtractor, min_eq_right hkn]
    rfl
  rw [hraw, Nat.mod_eq_of_lt hb]
  ac_rfl


/-- A computably scheduled, constant-loss extractor at its native seed length
extends to all larger supplied seed widths. -/
theorem constantLossFlatExtractor_of_native (ε : ℝ) (A Δ : ℕ)
    (baseSeed : ℕ × ℕ → ℕ) (base : ExtractorInput → ℕ)
    (hA : 0 < A)
    (hseed : ComputableInPolyTime baseSeed (encPair encUnary encNat) encUnary)
    (hbase : ComputableInPolyTime base encExtractorInput encNat)
    (hbound : ∀ n k : ℕ, 1 ≤ n → k ≤ n →
      baseSeed (n,k) ≤ A*(n.size+k.size^4) ∧ Δ ≤ k+baseSeed (n,k))
    (hstat : ∀ n k : ℕ, 1 ≤ n → k ≤ n →
      ∀ S : Finset (Fin (2^n)), 2^k ≤ S.card →
        FlatExtractorEvents (extractorEdge base Δ n k (baseSeed (n,k))) S ε) :
    ∃ (A Δ : ℕ) (extract : ExtractorInput → ℕ),
      0 < A ∧ ComputableInPolyTime extract encExtractorInput encNat ∧
      ∀ n k t : ℕ, 1 ≤ n → k ≤ n → A*(n.size+k.size^4) ≤ t → Δ ≤ k+t →
        ∀ S : Finset (Fin (2^n)), 2^k ≤ S.card →
          FlatExtractorEvents (extractorEdge extract Δ n k t) S ε := by
  refine ⟨A,Δ,padExtractor baseSeed base Δ,hA,padExtractor_polytime _ _ _ hseed hbase,?_⟩
  intro n k t hn hk ht _ S hS
  exact FlatExtractorEvents.padExtractor baseSeed base Δ n k t hk
    ((hbound n k hn hk).1.trans ht) (hbound n k hn hk).2 S ε (hstat n k hn hk S hS)

end TimeSpaceMA

namespace TimeSpaceMA

/-- The fourth power of a binary-encoding width is bounded by a fixed linear function
of the underlying positive integer. -/
private theorem tuz_size_four_le {n : ℕ} (hn : 0 < n) : n.size^4 ≤ 1296 * n := by
  have hh (t : ℕ) (ht : t ≥ 1) : t^4 ≤ 1296 * (2 : ℕ)^(t-1) := by
    induction t with
    | zero => omega
    | succ t ih =>
      by_cases ht6 : t < 6
      · have hb := Nat.pow_le_pow_left (show t+1 ≤ 6 by omega) 4
        have hp : 1 ≤ (2 : ℕ)^(t+1-1) := Nat.pow_pos (by decide)
        calc
          _ ≤ 6^4 := hb
          _ ≤ _ := by norm_num at *; omega
      · have h₁ : t^2 ≥ 36 := Nat.pow_le_pow_left (show 6 ≤ t by omega) 2
        have h₂ : 6*t^2 ≤ t^3 := by
          rw [show t^3 = t^2 * t by ring, Nat.mul_comm 6]
          exact Nat.mul_le_mul_left _ (by omega)
        have h₃ : 6*t^3 ≤ t^4 := by
          rw [show t^4 = t^3 * t by ring, Nat.mul_comm 6]
          exact Nat.mul_le_mul_left _ (by omega)
        have h4 : (t+1)^4 ≤ 2*t^4 := by
          have hlow : 6*t^2 + 4*t + 1 ≤ 2*t^3 := by nlinarith
          nlinarith
        calc
          _ ≤ 2*t^4 := h4
          _ ≤ 2*(1296*2^(t-1)) := Nat.mul_le_mul_left _ (ih (by omega))
          _ = _ := by
            rw [show t+1-1 = (t-1)+1 by omega, pow_succ]
            ac_rfl
  have hsize := Nat.size_pos.mpr hn
  have hpow : (2 : ℕ)^(n.size-1) ≤ n := Nat.lt_size.mp (by omega)
  exact (hh n.size hsize).trans (Nat.mul_le_mul_left _ hpow)

private theorem bitWidth_mul_le (a b : ℕ) : (a*b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self _) (Nat.lt_size_self _)

private theorem bitWidth_pos_le_cube {a : ℕ} (ha : 0 < a) : a.size^3 ≤ 1296*a := by
  have hq : 1 ≤ a.size := Nat.size_pos.mpr ha
  have h := Nat.pow_le_pow_right (show 0 < a.size by omega) (show (3:ℕ) ≤ 4 by decide)
  exact h.trans (tuz_size_four_le ha)

/-- The second extractor's polylogarithmic seed is controlled by the original entropy
and the original input's logarithm, because the condenser's output has width 2(k+d). -/
theorem guv_rrv_seed_bound (a b Δ : ℕ) :
    ∃ A : ℕ, 0 < A ∧ ∀ n k : ℕ, 1 ≤ n →
      a*n.size + (b*(2*(k+a*n.size)).size^3 + Δ) ≤ A*(n.size+k.size^4) := by
  let C := 3 + a.size
  let A := a + b*(9*(C^3+1296+1)) + Δ + 1
  refine ⟨A, by dsimp [A]; omega, ?_⟩
  intro n k hn
  let q := n.size
  let h := k.size
  let p := q.size
  have hq : 1 ≤ q := Nat.size_pos.mpr hn
  have hkw : (2*(k+a*q)).size ≤ C + h + p := by
    calc
      _ ≤ (2:ℕ).size + (k+a*q).size := bitWidth_mul_le _ _
      _ ≤ (2:ℕ).size + (k.size+(a*q).size+1) := Nat.add_le_add_left (Nat.size_add_le _ _) _
      _ ≤ _ := by
        have hh := bitWidth_mul_le a q
        dsimp [C, h, p]
        change 2 + (k.size+(a*q).size+1) ≤ _
        omega
  have hcube : (C+h+p)^3 ≤ 9*(C^3+h^3+p^3) := by
    have harm (x y z : ℕ) : 2*x^3+y^3 ≥ 3*x^2*y := by
      have hp : 0 ≤ ((x:ℤ)-(y:ℤ))^2*(2*(x:ℤ)+(y:ℤ)) := by positivity
      have h' : 3*(x:ℤ)^2*(y:ℤ) ≤ 2*(x:ℤ)^3+(y:ℤ)^3 := by nlinarith
      exact_mod_cast h'
    nlinarith [harm C h p, harm C p h, harm h C p, harm h p C,
      harm p C h, harm p h C]
  have hmono : (2*(k+a*q)).size^3 ≤ (C+h+p)^3 := Nat.pow_le_pow_left hkw 3
  have hpcube : p^3 ≤ 1296*q := bitWidth_pos_le_cube (by omega : 0 < q)
  have hhcube : h^3 ≤ h^4 := by
    by_cases hz : h = 0
    · simp [hz]
    · exact Nat.pow_le_pow_right (by omega : 0 < h) (by decide)
  have hCcube : C^3 ≤ C^3*q := by simpa using Nat.mul_le_mul_left (C^3) hq
  have htotal : (2*(k+a*q)).size^3 ≤ 9*(C^3+1296+1)*(q+h^4) := by
    have hscaled : C^3+h^3+p^3 ≤ C^3*q+h^4+1296*q := by omega
    calc
      _ ≤ 9*(C^3+h^3+p^3) := hmono.trans hcube
      _ ≤ 9*(C^3*q+h^4+1296*q) := Nat.mul_le_mul_left _ hscaled
      _ ≤ 9*((C^3+1296+1)*(q+h^4)) := by
        apply Nat.mul_le_mul_left
        rw [Nat.mul_add]
        have hq' : C^3*q+1296*q ≤ (C^3+1296+1)*q := by
          rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
          omega
        have hh' : h^4 ≤ (C^3+1296+1)*h^4 := by
          simpa using Nat.mul_le_mul_right (h^4) (show 1 ≤ C^3+1296+1 by omega)
        omega
      _ = _ := by ring
  change a*q + (b*(2*(k+a*q)).size^3+Δ) ≤ A*(q+h^4)
  have hbig := Nat.mul_le_mul_left b htotal
  have hΔ : Δ ≤ Δ*q := by simpa using Nat.mul_le_mul_left Δ hq
  have haq : a*q ≤ a*(q+h^4) := Nat.mul_le_mul_left a (by omega)
  have hΔ' : Δ*q ≤ Δ*(q+h^4) := Nat.mul_le_mul_left Δ (by omega)
  dsimp only [A]
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
  omega

end TimeSpaceMA

open scoped BigOperators

namespace TimeSpaceMA

section Statistics

variable {X Y Seed₁ Seed₂ Out : Type} [Fintype Y] [Fintype Seed₁] [Fintype Seed₂] [Fintype Out]
  [DecidableEq Y] [DecidableEq Out]

/-- A lossless condenser followed by a seeded extractor loses only the sum of their
statistical errors. This finite version uses event excess directly and avoids any
distinction between equalities of measurable spaces. -/
theorem FlatExtractorEvents.ofLosslessCondenser
    (cond : X → Seed₁ → Y) (ext : Y → Seed₂ → Out) (S : Finset X)
    (reference : Y → ℝ) (δ ε : ℝ) (hseed : 0 < Fintype.card Seed₂)
    (hcond : CondensesFlatEvents cond S reference δ)
    (hext : WeightedExtractorEvents ext reference ε) :
    FlatExtractorEvents (fun x (s : Seed₁ × Seed₂) => ext (cond x s.1) s.2) S (δ+ε) := by
  classical
  intro U
  let V := fun r : Seed₂ => Finset.univ.filter (fun y : Y => ext y r ∈ U)
  let F := fun r : Seed₂ => (S ×ˢ Finset.univ).filter
    (fun p : X × Seed₁ => cond p.1 p.2 ∈ V r)
  let G := (S ×ˢ Finset.univ).filter
    (fun p : X × (Seed₁ × Seed₂) => ext (cond p.1 p.2.1) p.2.2 ∈ U)
  have hV (r : Seed₂) (y : Y) : y ∈ V r ↔ ext y r ∈ U := by simp [V]
  have hcount : G.card = ∑ r : Seed₂, (F r).card := by
    rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
    simp only [Finset.sum_product]
    conv_rhs => enter [2, r]; rw [Finset.card_filter, Finset.sum_product]
    simp only [hV]
    trans ∑ x ∈ S, ∑ r : Seed₂, ∑ s : Seed₁, if ext (cond x s) r ∈ U then 1 else 0
    · apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    · rw [Finset.sum_comm]
  have hcast : (G.card : ℝ) = ∑ r : Seed₂, ((F r).card : ℝ) := by exact_mod_cast hcount
  let a : ℝ := (S.card : ℝ) * Fintype.card Seed₁
  let d : ℝ := Fintype.card Seed₂
  have hd : 0 < d := by dsimp [d]; exact_mod_cast hseed
  have htest (r : Seed₂) : ((F r).card : ℝ) / a - ∑ y ∈ V r, reference y ≤ δ :=
    hcond (V r)
  have hsum : (∑ r : Seed₂, (((F r).card : ℝ) / a - ∑ y ∈ V r, reference y)) ≤ d*δ := by
    calc
      _ ≤ ∑ _ : Seed₂, δ := Finset.sum_le_sum (fun r _ => htest r)
      _ = _ := by simp [nsmul_eq_mul, d]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← hcast] at hsum
  have hweight : (∑ r : Seed₂, ∑ y ∈ V r, reference y) / d =
      weightedExtractionProbability ext reference U := by
    rw [weightedExtractionProbability, ← Finset.sum_div]
    congr 1
    simp_rw [V, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    split <;> simp
  have hG : (G.card : ℝ) / (a*d) - weightedExtractionProbability ext reference U ≤ δ := by
    rw [← hweight, ← div_div, ← sub_div]
    exact (div_le_iff₀ hd).mpr (by simpa [mul_comm] using hsum)
  have hE := hext U
  change (G.card : ℝ) / ((S.card : ℝ) * (Fintype.card (Seed₁ × Seed₂) : ℝ)) -
    (U.card : ℝ) / (Fintype.card Out : ℝ) ≤ δ+ε
  rw [Fintype.card_prod, Nat.cast_mul, ← mul_assoc]
  change (G.card : ℝ) / (a*d) - (U.card : ℝ) / (Fintype.card Out : ℝ) ≤ δ+ε
  linarith

end Statistics

end TimeSpaceMA

namespace TimeSpaceMA

open Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- The logarithmic seed bound is amortized by first condensing to width
(2(k+a,mathrm{size}(n))), then using the constant-loss extractor at that width. -/
def guvRrvSeed (a b Δ : ℕ) (p : ℕ × ℕ) : ℕ :=
  let K := min p.1 p.2 + a*p.1.size
  a*p.1.size + (b*(2*K).size^3+Δ)

/-- The combined source uses the first part of its seed to condense the input
and the remainder as the second extractor's independent seed. -/
def guvRrvExtractor (cond ext : ExtractorInput → ℕ) (a b Δ : ℕ) : ExtractorInput → ℕ :=
  fun (n,k,_,x,y) =>
    let k := min n k
    let d₁ := a*n.size
    let K := k+d₁
    let w := 2*K
    let d₂ := b*w.size^3+Δ
    let radix := (2:ℕ)^d₂
    let z := cond (n,k,d₁,x,y/radix) % 2^w
    ext (w,K,d₂,z,y%radix)

private theorem extract_size_u {α : Type} {input : α ↪ List Bool} {v : α → ℕ}
    (h : ComputableTidilyInPolyTime v input encUnary) :
    ComputableTidilyInPolyTime (fun x => (v x).size) input encUnary :=
  ComputableInPolyTime.binary_size.tidy.comp (unary_to_binary.comp h)

private theorem extract_clamp {α : Type} {input : α ↪ List Bool} {n k : α → ℕ}
    (hn : ComputableTidilyInPolyTime n input encUnary)
    (hk : ComputableTidilyInPolyTime k input encNat) :
    ComputableTidilyInPolyTime (fun x => min (n x) (k x)) input encUnary :=
  (ComputableInPolyTime.binary_min_unary' hn.computableInPolyTime hk.computableInPolyTime).tidy

private theorem guv_seed_u {α : Type} {input : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableTidilyInPolyTime n input encUnary) (a : ℕ) :
    ComputableTidilyInPolyTime (fun x => a*(n x).size) input encUnary :=
  unary_mul.comp ((const a).prod (extract_size_u hn))

private theorem rrv_seed_u {α : Type} {input : α ↪ List Bool} {w : α → ℕ}
    (hw : ComputableTidilyInPolyTime w input encUnary) (b Δ : ℕ) :
    ComputableTidilyInPolyTime (fun x => b*(w x).size^3+Δ) input encUnary :=
  unary_add.comp ((unary_mul.comp ((const b).prod
    ((unary_pow 3).comp (extract_size_u hw)))).prod (const Δ))

private theorem guvRrvSeed_polytime (a b Δ : ℕ) :
    ComputableInPolyTime (guvRrvSeed a b Δ) (encPair encUnary encNat) encUnary := by
  apply ComputableTidilyInPolyTime.computableInPolyTime
  have hn := fst encUnary encNat
  have hk := extract_clamp hn (snd encUnary encNat)
  have hd := guv_seed_u hn a
  have hK := unary_add.comp (hk.prod hd)
  have hw := unary_mul.comp ((const 2).prod hK)
  exact unary_add.comp (hd.prod (rrv_seed_u hw b Δ))

private theorem guvRrvExtractor_polytime (a b Δ : ℕ) (cond ext : ExtractorInput → ℕ)
    (hcond : ComputableInPolyTime cond encExtractorInput encNat)
    (hext : ComputableInPolyTime ext encExtractorInput encNat) :
    ComputableInPolyTime (guvRrvExtractor cond ext a b Δ) encExtractorInput encNat := by
  apply ComputableTidilyInPolyTime.computableInPolyTime
  let input := encExtractorInput
  have hn : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.1) input encUnary := fst _ _
  have hkraw : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.2.1) input encNat :=
    (snd _ _).fst'
  have hx : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.2.2.2.1) input encNat :=
    (snd _ _).snd'.snd'.fst'
  have hy : ComputableTidilyInPolyTime (fun p : ExtractorInput => p.2.2.2.2) input encNat :=
    (snd _ _).snd'.snd'.snd'
  have hk := extract_clamp hn hkraw
  have hd := guv_seed_u hn a
  have hK := unary_add.comp (hk.prod hd)
  have hw := unary_mul.comp ((const 2).prod hK)
  have hd' := rrv_seed_u hw b Δ
  have hradix := binary_two_pow.comp hd'
  have hz0 := hcond.tidy.comp (hn.prod ((unary_to_binary.comp hk).prod
    (hd.prod (hx.prod (binary_div' hy hradix)))))
  have hz := binary_mod' hz0 (binary_two_pow.comp hw)
  exact hext.tidy.comp (hw.prod ((unary_to_binary.comp hK).prod
    (hd'.prod (hz.prod (binary_mod' hy hradix)))))

private theorem guvRrv_flat (ε₁ ε₂ : ℝ) (a b Δ : ℕ)
    (cond ext : ExtractorInput → ℕ) (ha : 0 < a)
    (hcond : ∀ n k : ℕ, 1 ≤ n → k ≤ n →
      let s := a*n.size
      let m := 2*(k+s)
      ∀ S : Finset (Fin (2^n)), 2^k ≤ S.card →
        ∃ q : Fin (2^m) → ℝ, (∑ y, q y) = 1 ∧
          (∀ y, 0 ≤ q y ∧ q y ≤ 1/(2:ℝ)^(k+s)) ∧
          CondensesFlatEvents (fixedOutput cond n k s m) S q ε₁)
    (hext : ∀ w K : ℕ, 1 ≤ w → K ≤ w →
      let d := b*w.size^3+Δ
      ∀ q : Fin (2^w) → ℝ, (∑ y, q y) = 1 →
        (∀ y, 0 ≤ q y ∧ q y ≤ 1/(2:ℝ)^K) →
        WeightedExtractorEvents (extractorEdge ext Δ w K d) q ε₂)
    (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) (S : Finset (Fin (2^n))) (hS : 2^k ≤ S.card) :
    FlatExtractorEvents
      (extractorEdge (guvRrvExtractor cond ext a b Δ) Δ n k (guvRrvSeed a b Δ (n,k)))
      S (ε₁+ε₂) := by
  let d₁ := a*n.size
  let K := k+d₁
  let w := 2*K
  let d₂ := b*w.size^3+Δ
  have hw : 1 ≤ w := by
    have hd : 0 < d₁ := Nat.mul_pos ha (Nat.size_pos.mpr hn)
    dsimp [w,K]
    omega
  have hK : K ≤ w := by dsimp [w]; omega
  obtain ⟨q,hq,hcap,hqcond⟩ := hcond n k hn hk S hS
  have hqe := hext w K hw hK q hq hcap
  have hF := FlatExtractorEvents.ofLosslessCondenser
    (fixedOutput cond n k d₁ w) (extractorEdge ext Δ w K d₂) S q ε₁ ε₂
    (by simp) hqcond hqe
  have hwidth : K+d₂-Δ = k+(d₁+d₂)-Δ := by dsimp only [K]; omega
  let eOut : Fin (2^(K+d₂-Δ)) ≃ Fin (2^(k+(d₁+d₂)-Δ)) :=
    finCongr (congrArg (fun z : ℕ => 2^z) hwidth)
  have heft := FlatExtractorEvents.equivSeedOutput _ S (ε₁+ε₂)
    (paddedSeedEquiv d₁ d₂) eOut hF
  have hseed : guvRrvSeed a b Δ (n,k) = d₁+d₂ := by
    simp [guvRrvSeed,min_eq_right hk,d₁,d₂,w,K]
  rw [hseed]
  convert heft using 2
  rename_i x
  funext y
  apply Fin.ext
  change guvRrvExtractor cond ext a b Δ (n,k,d₁+d₂,x.val,y.val) % 2^(k+(d₁+d₂)-Δ) =
    ext (w,K,d₂,cond (n,k,d₁,x.val,y.val/2^d₂) % 2^w,y.val % 2^d₂) % 2^(K+d₂-Δ)
  simp [guvRrvExtractor,min_eq_right hk,d₁,d₂,w,K,Nat.add_assoc]


/-- GUV and RRV together imply the exact constant-loss, padded flat-extractor
interface used in the disperser construction. -/
theorem constantLossFlatExtractor_from_guv_rrv
    (ε : ℝ) (hGUV : HasShortLosslessCondenser (ε/2))
    (hRRV : HasPolylogConstantLossExtractor (ε/2)) :
    ∃ (A Δ : ℕ) (extract : ExtractorInput → ℕ),
      0 < A ∧ ComputableInPolyTime extract encExtractorInput encNat ∧
      ∀ n k t : ℕ, 1 ≤ n → k ≤ n → A*(n.size+k.size^4) ≤ t → Δ ≤ k+t →
        ∀ S : Finset (Fin (2^n)), 2^k ≤ S.card →
          FlatExtractorEvents (extractorEdge extract Δ n k t) S ε := by
  obtain ⟨a,cond,ha,hc,hcond⟩ := hGUV
  obtain ⟨b,Δ,ext,_,he,hext⟩ := hRRV
  obtain ⟨A,hA,hseed⟩ := guv_rrv_seed_bound a b Δ
  apply constantLossFlatExtractor_of_native ε A Δ (guvRrvSeed a b Δ)
    (guvRrvExtractor cond ext a b Δ) hA (guvRrvSeed_polytime _ _ _)
    (guvRrvExtractor_polytime _ _ _ _ _ hc he)
  · intro n k hn hk
    refine ⟨?_,?_⟩
    · simpa [guvRrvSeed,min_eq_right hk] using hseed n k hn
    · simp [guvRrvSeed]; omega
  · intro n k hn hk S hS
    rw [show ε = ε/2+ε/2 by ring]
    exact guvRrv_flat _ _ _ _ _ _ _ ha hcond hext n k hn hk S hS

end TimeSpaceMA

open TimeSpaceMA Turing.MultiTapeTM

/-- Compose the lossless condenser and constant-loss extractor, with independent padding. -/
theorem solution (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1/4) :
    ∃ (A Δ : ℕ) (extract : ExtractorInput → ℕ),
      0 < A ∧ ComputableInPolyTime extract encExtractorInput encNat ∧
      ∀ n k t : ℕ, 1 ≤ n → k ≤ n → A*(n.size+k.size^4) ≤ t → Δ ≤ k+t →
        ∀ S : Finset (Fin (2^n)), 2^k ≤ S.card →
          FlatExtractorEvents (extractorEdge extract Δ n k t) S ε := by
  have hp : 0 < ε/2 := by linarith
  have hq : ε/2 ≤ (1:ℝ)/8 := by linarith
  exact constantLossFlatExtractor_from_guv_rrv ε
    (shortLosslessCondenser _ hp hq) (polylogConstantLossExtractor _ hp hq)
