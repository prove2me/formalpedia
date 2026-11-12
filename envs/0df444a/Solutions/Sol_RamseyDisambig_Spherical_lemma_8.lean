-- Prove2me | solution 1 for RamseyDisambig.Spherical.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:03:10.149978+00:00
-- url     : https://prove2.me/submissions/136f7dfc-4c84-4787-86e6-2c188707ebb8

import Mathlib
import Definitions.Def_RamseyDisambig_Spherical_GapColoring
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_RamseyDisambig_Spherical_Torus

section
set_option autoImplicit false

namespace RamseyDisambig.Dev.Basics

open RamseyDisambig.Spherical NatureSLT.GrowthFunction

/-- Shattered family gives vcDim ≥ its size. -/
theorem le_vcDim_of_shatters {Z Λ : Type*} (Q : Λ → Z → Bool) {h : ℕ} (z : Fin h → Z)
    (hz : Shatters Q z) : (h : ℕ∞) ≤ vcDim Q := by
  unfold vcDim
  exact le_iSup₂_of_le h ⟨z, hz⟩ le_rfl

end RamseyDisambig.Dev.Basics
end

section
set_option autoImplicit false

namespace RamseyDisambig.Dev.L8

open RamseyDisambig.Spherical NatureSLT.GrowthFunction

section
variable {R : ℕ+} {n : ℕ}

def tor (v : Fin n → ℕ) : Torus R n := fun j => ((v j : ℕ) : ZMod (R : ℕ))

lemma cd_nat (u v : ℕ) (hu : u < (R:ℕ)) (hv : v < (R:ℕ)) :
    cyclicDistance (R := R) (u : ZMod (R:ℕ)) (v : ZMod (R:ℕ)) =
      min |(u:ℝ) - v| ((R:ℝ) - |(u:ℝ) - v|) := by
  unfold cyclicDistance
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv]

lemma cd_eq (u v w : ℕ) (hu : u < (R:ℕ)) (hv : v < (R:ℕ)) (h : u = v + w ∨ v = u + w)
    (hw : 2 * w ≤ (R:ℕ)) :
    cyclicDistance (R := R) (u : ZMod (R:ℕ)) (v : ZMod (R:ℕ)) = w := by
  rw [cd_nat u v hu hv]
  have habs : |(u:ℝ) - v| = w := by
    rcases h with h | h
    · rw [h]; push_cast; simp
    · rw [h]; push_cast; rw [abs_sub_comm]; simp
  rw [habs]
  have : (2:ℝ) * w ≤ (R:ℝ) := by exact_mod_cast hw
  exact min_eq_left (by linarith)

lemma cd_le_half (x y : ZMod (R:ℕ)) : 2 * cyclicDistance x y ≤ (R:ℝ) := by
  unfold cyclicDistance
  have h1 := min_le_left (|(x.val : ℝ) - (y.val : ℝ)|) ((R : ℝ) - |(x.val : ℝ) - (y.val : ℝ)|)
  have h2 := min_le_right (|(x.val : ℝ) - (y.val : ℝ)|) ((R : ℝ) - |(x.val : ℝ) - (y.val : ℝ)|)
  linarith

lemma dist0 (r : ℕ) (hR : (R:ℕ) = 2 * r) (hr0 : 0 < r) (a : Fin n → ℕ) (ha : ∀ j, a j ≤ r) :
    torusDistance (tor (fun _ => 0) : Torus R n) (tor a) = ∑ j, (a j : ℝ) := by
  unfold torusDistance distanceProfile
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have := ha j
  exact cd_eq (R := R) 0 (a j) (a j) (by omega) (by omega) (Or.inr (by omega)) (by omega)

lemma diam (r : ℕ) (hR : (R:ℕ) = 2 * r) (hr0 : 0 < r) :
    finiteDiameter (torusDistance (R := R) (n := n)) = n * r := by
  unfold finiteDiameter
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, ⟨(0, 0), rfl⟩⟩
    · rintro _ ⟨⟨x, y⟩, rfl⟩
      simp only [torusDistance, distanceProfile]
      calc ∑ i, cyclicDistance (x i) (y i) ≤ ∑ _i : Fin n, (r:ℝ) :=
            Finset.sum_le_sum (fun i _ => by
              have := cd_le_half (x i) (y i)
              have hR' : (R:ℝ) = 2 * r := by exact_mod_cast hR
              linarith)
        _ = n * r := by simp
  · have hb : BddAbove (Set.range fun p : Torus R n × Torus R n => torusDistance p.1 p.2) :=
      (Set.finite_range _).bddAbove
    refine le_trans ?_ (le_csSup hb ⟨(tor (fun _ => 0), tor (fun _ => r)), rfl⟩)
    show (n:ℝ) * r ≤ torusDistance (tor (fun _ => 0) : Torus R n) (tor (fun _ => r))
    rw [dist0 r hR hr0 _ (fun _ => le_rfl)]
    simp

def av (s : ℕ) (e : Fin n → Fin (s+1)) : Fin n → ℕ := fun j => 3 ^ (e j : ℕ)

lemma av_le (s : ℕ) (e : Fin n → Fin (s+1)) (j : Fin n) : av s e j ≤ 3 ^ s :=
  Nat.pow_le_pow_right (by norm_num) (Nat.lt_succ_iff.mp (e j).2)

lemma av_lt (s : ℕ) (e : Fin n → Fin (s+1)) (j : Fin n) (h : (e j : ℕ) < s) :
    3 * av s e j ≤ 3 ^ s := by
  unfold av
  calc 3 * 3 ^ (e j : ℕ) = 3 ^ ((e j : ℕ) + 1) := by ring
    _ ≤ 3 ^ s := Nat.pow_le_pow_right (by norm_num) h

end

open Classical in
theorem main (s n q : ℕ) (ε : ℝ) (hs : 1 / (3:ℝ) ^ s ≤ ε) (hnq : (q:ℝ) ≤ ε * n)
    (R : ℕ+) (hR : (R:ℕ) = 2 * 3 ^ s) (c : Torus R n → Torus R n → Bool)
    (hgap : GapColoring ε torusDistance c) (hcan : DistanceProfileCanonical c) :
    ∃ z : Fin q → Torus R n, Shatters c z := by
  have hr0 : 0 < 3 ^ s := by positivity
  have hr0' : (0:ℝ) < (3:ℝ) ^ s := by positivity
  have hdiam := diam (R := R) (n := n) (3 ^ s) hR hr0
  obtain ⟨hlo, hhi⟩ := hgap
  rw [hdiam] at hlo hhi
  have hεr : 1 ≤ ε * (3:ℝ) ^ s := by
    have := mul_le_mul_of_nonneg_right hs hr0'.le
    rwa [one_div, inv_mul_cancel₀ hr0'.ne'] at this
  let F : Finset (Fin n → Fin (s+1)) :=
    Finset.univ.filter (fun e => c (tor (fun _ => 0)) (tor (av s e)) = false)
  have hF : F.Nonempty := by
    refine ⟨fun _ => 0, ?_⟩
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
    apply hlo
    rw [dist0 (3 ^ s) hR hr0 _ (av_le s _)]
    simp only [av]
    simp
    nlinarith
  obtain ⟨e, heF, hmax⟩ := Finset.exists_max_image F (fun e => ∑ j, av s e j) hF
  have hce : c (tor (fun _ => 0)) (tor (av s e)) = false := by
    simpa [F] using heF
  -- counting
  have hcard : (q:ℝ) ≤ ((Finset.univ.filter (fun j : Fin n => (e j : ℕ) < s)).card : ℝ) := by
    have hlt : ¬ ((1 - ε) * (n * (3 ^ s : ℕ)) ≤ torusDistance (tor (fun _ => 0) : Torus R n)
        (tor (av s e))) := by
      intro h
      have := hhi _ _ h
      rw [hce] at this
      exact Bool.false_ne_true this
    rw [dist0 (3 ^ s) hR hr0 _ (av_le s _)] at hlt
    push Not at hlt
    set Jc := Finset.univ.filter (fun j : Fin n => ¬ (e j : ℕ) < s) with hJc
    have hsum : ((3 ^ s : ℕ) : ℝ) * Jc.card ≤ ∑ j, (av s e j : ℝ) := by
      calc ((3 ^ s : ℕ) : ℝ) * Jc.card = ∑ _j ∈ Jc, ((3 ^ s : ℕ) : ℝ) := by simp [mul_comm]
        _ ≤ ∑ j ∈ Jc, (av s e j : ℝ) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          have hj' : ¬ (e j : ℕ) < s := (Finset.mem_filter.mp hj).2
          have : (e j : ℕ) = s := le_antisymm (Nat.lt_succ_iff.mp (e j).2) (not_lt.mp hj')
          simp [av, this]
        _ ≤ ∑ j, (av s e j : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
    have hr' : (0:ℝ) < ((3 ^ s : ℕ) : ℝ) := by exact_mod_cast hr0
    have h1 : (Jc.card : ℝ) < (1 - ε) * n := by
      by_contra h
      push Not at h
      have := mul_le_mul_of_nonneg_left h hr'.le
      nlinarith
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun j : Fin n => (e j : ℕ) < s)
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    have h3 : ((Finset.univ.filter (fun j : Fin n => (e j : ℕ) < s)).card : ℝ) + Jc.card = n := by
      exact_mod_cast h2
    linarith
  have hq : q ≤ Fintype.card {j : Fin n // (e j : ℕ) < s} := by
    rw [Fintype.card_subtype]
    exact_mod_cast hcard
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le (α := Fin q)
    (β := {j : Fin n // (e j : ℕ) < s}) (by simpa using hq)
  -- the points and rows
  let xv : Fin n → Fin n → ℕ := fun i j => if (e j : ℕ) < s ∧ j ≠ i then 2 * av s e j else 0
  let yv : (Fin n → Bool) → Fin n → ℕ :=
    fun p j => if (e j : ℕ) < s ∧ p j = true then 3 * av s e j else av s e j
  have key : ∀ (i : Fin n), (e i : ℕ) < s → ∀ p : Fin n → Bool,
      c (tor (yv p)) (tor (xv i)) = p i := by
    intro i hi p
    let a' : Fin n → ℕ := fun j => if j = i ∧ p i = true then 3 * av s e j else av s e j
    have h1 : c (tor (yv p)) (tor (xv i)) = c (tor (fun _ => 0)) (tor a') := by
      apply hcan
      funext j
      simp only [distanceProfile, tor]
      have hA := av_le s e j
      have hA3 := av_lt s e j
      have hR' := hR
      by_cases hji : j = i
      · subst hji
        have hx : xv j j = 0 := by simp [xv]
        have hy : yv p j = a' j := by
          by_cases hp : p j = true <;> simp [yv, a', hp, hi]
        have ha' : a' j ≤ 3 ^ s := by
          by_cases hp : p j = true
          · simp [a', hp]; exact hA3 hi
          · simp [a', hp]; exact hA
        have e1 := cd_eq (R := R) (yv p j) (xv j j) (a' j) (by omega) (by omega)
          (Or.inl (by omega)) (by omega)
        have e2 := cd_eq (R := R) 0 (a' j) (a' j) (by omega) (by omega)
          (Or.inr (by omega)) (by omega)
        rw [e1, e2]
      · have ha' : a' j = av s e j := by simp [a', hji]
        have e2 := cd_eq (R := R) 0 (a' j) (a' j) (by omega) (by omega)
          (Or.inr (by omega)) (by omega)
        by_cases hej : (e j : ℕ) < s
        · have hx : xv i j = 2 * av s e j := by simp [xv, hej, hji]
          have hA3' := hA3 hej
          rw [e2]
          by_cases hp : p j = true
          · have hy : yv p j = 3 * av s e j := by simp [yv, hej, hp]
            have := cd_eq (R := R) (yv p j) (xv i j) (av s e j) (by omega) (by omega)
              (Or.inl (by omega)) (by omega)
            rw [this, ha']
          · have hy : yv p j = av s e j := by simp [yv, hp]
            have := cd_eq (R := R) (yv p j) (xv i j) (av s e j) (by omega) (by omega)
              (Or.inr (by omega)) (by omega)
            rw [this, ha']
        · have hx : xv i j = 0 := by simp [xv, hej]
          have hy : yv p j = av s e j := by simp [yv, hej]
          rw [e2]
          have := cd_eq (R := R) (yv p j) (xv i j) (av s e j) (by omega) (by omega)
            (Or.inl (by omega)) (by omega)
          rw [this, ha']
    rw [h1]
    by_cases hp : p i = true
    · rw [hp]
      let e' : Fin n → Fin (s+1) := Function.update e i ⟨(e i : ℕ) + 1, by omega⟩
      have hav' : ∀ j, av s e' j = a' j := by
        intro j
        by_cases hji : j = i
        · subst hji
          simp [av, e', a', hp, pow_succ, mul_comm]
        · simp [av, e', a', hji, Function.update_of_ne hji]
      have ha'e : a' = av s e' := funext fun j => (hav' j).symm
      rw [ha'e]
      by_contra hne
      have hf : c (tor (fun _ => 0)) (tor (av s e')) = false := by
        simpa using hne
      have hmem : e' ∈ F := by simp [F, hf]
      have hle := hmax e' hmem
      have hlt : ∑ j, av s e j < ∑ j, av s e' j := by
        refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
        · rw [hav' j]; by_cases hji : j = i <;> simp [a', hji, hp] <;> omega
        · rw [hav' i]; have : 0 < av s e i := by simp [av]
          simp [a', hp]; omega
      omega
    · have hp' : p i = false := by simpa using hp
      have : a' = av s e := funext fun j => by simp [a', hp']
      rw [this, hce, hp']
  refine ⟨fun k => tor (xv (ι k).1), fun δ => ?_⟩
  refine ⟨tor (yv (fun j => decide (∃ k, (ι k).1 = j ∧ δ k = true))), fun k => ?_⟩
  rw [key (ι k).1 (ι k).2]
  by_cases hk : δ k = true
  · have h : ∃ k', (ι k').1 = (ι k).1 ∧ δ k' = true := ⟨k, rfl, hk⟩
    simp [h, hk]
  · have hkf : δ k = false := by simpa using hk
    have h : ¬ ∃ k', (ι k').1 = (ι k).1 ∧ δ k' = true := by
      rintro ⟨k', h1, h2⟩
      have := ι.injective (Subtype.ext h1)
      subst this
      exact hk h2
    simp [h, hkf]

end RamseyDisambig.Dev.L8

namespace RamseyDisambig.Spherical

theorem chk_lemma_8 (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) (q : ℕ) (hq : 1 ≤ q) :
    ∃ (n : ℕ) (R : ℕ+), 1 ≤ n ∧ 2 ≤ (R : ℕ) ∧ Even (R : ℕ) ∧
      ∀ c : Torus R n → Torus R n → Bool,
        GapColoring ε torusDistance c → DistanceProfileCanonical c →
          (q : ℕ∞) ≤ NatureSLT.GrowthFunction.vcDim c := by
  obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/3:ℝ) < 1)
  have hs' : 1 / (3:ℝ) ^ s ≤ ε := by rw [← one_div_pow]; exact hs.le
  have hpos : 0 < 3 ^ s := by positivity
  refine ⟨⌈(q:ℝ) / ε⌉₊ + 1, ⟨2 * 3 ^ s, by omega⟩, by omega, by simp; omega, ⟨3 ^ s, by simp; ring⟩, ?_⟩
  intro c hgap hcan
  have hnq : (q:ℝ) ≤ ε * ((⌈(q:ℝ) / ε⌉₊ + 1 : ℕ) : ℝ) := by
    have h1 : (q:ℝ) / ε ≤ ⌈(q:ℝ) / ε⌉₊ := Nat.le_ceil _
    rw [div_le_iff₀ hε] at h1
    push_cast
    nlinarith
  obtain ⟨z, hz⟩ := Dev.L8.main s _ q ε hs' hnq ⟨2 * 3 ^ s, by omega⟩ rfl c hgap hcan
  exact Dev.Basics.le_vcDim_of_shatters c z hz

end RamseyDisambig.Spherical
end

theorem solution : type_of% @RamseyDisambig.Spherical.chk_lemma_8 := @RamseyDisambig.Spherical.chk_lemma_8
