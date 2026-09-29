-- Prove2me | solution 1 for bernoulli_sampled_row_column_energy_controlled_log_moment_bound_2pN
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-25T06:23:03.685148+00:00
-- url     : https://prove2.me/submissions/0552b083-e535-4493-9b66-4de5a229fc99

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_sampled_counts
import Mathlib

/-!
# `bernoulli_sampled_row_column_energy_log_moment_bound` (platform node 4337294c)

Self-contained proof using the RELAXED CR2008 Lemma 6.2 (binomial card moment
bounded by `(2x)^q` for any scale `x ≥ n·p` with `q ≤ x`).  Choosing the scale
`x := 2·(n·p)` extends the validity window from `q ≤ n·p` to `q ≤ 2·n·p`, which
is exactly what the one-sample lower bound `m ≥ β·N·log N` (N = max n₁ n₂) can
supply for the exponent `q := ⌈β log N⌉`.

Constant: `C = 8·e`.

All inlined bricks (`CR2008Lemma62`, `Marginal`, `CR2008Lemma62Max`) and the two
energy↔count bridges are reproduced here so the file is self-contained on Mathlib
plus the platform Definitions.
-/

open scoped BigOperators

/-! ## Brick 1 : single-row binomial card moment (relaxed Lemma 6.2) -/

namespace CR2008Lemma62

noncomputable def rowBernoulliMoment (n q : ℕ) (p : ℝ) : ℝ :=
  ∑ S : Finset (Fin n),
    p ^ S.card * (1 - p) ^ (n - S.card) * (S.card : ℝ) ^ q

noncomputable def binomCardMoment (n q : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    ((n.choose k : ℕ) : ℝ) * p ^ k * (1 - p) ^ (n - k) * (k : ℝ) ^ q

lemma rowBernoulliMoment_eq_binomCardMoment (n q : ℕ) (p : ℝ) :
    rowBernoulliMoment n q p = binomCardMoment n q p := by
  classical
  unfold rowBernoulliMoment binomCardMoment
  let U : Finset (Fin n) := Finset.univ
  have hUcard : U.card = n := by simp [U]
  have h_univ :
      (Finset.univ : Finset (Finset (Fin n))) = U.powerset := by
    ext S
    simp [U]
  rw [h_univ, Finset.sum_powerset, hUcard]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hconst : ∀ t ∈ Finset.powersetCard k U,
      p ^ t.card * (1 - p) ^ (n - t.card) * (t.card : ℝ) ^ q
        = p ^ k * (1 - p) ^ (n - k) * (k : ℝ) ^ q := by
    intro t ht
    rw [(Finset.mem_powersetCard.mp ht).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard, hUcard,
      nsmul_eq_mul]
  ring

lemma binomCardMoment_zero (n : ℕ) (p : ℝ) :
    binomCardMoment n 0 p = 1 := by
  unfold binomCardMoment
  have h := add_pow p (1 - p) n
  have hsum :
      (∑ k ∈ Finset.range (n + 1),
        p ^ k * (1 - p) ^ (n - k) * ((n.choose k : ℕ) : ℝ)) = 1 := by
    calc
      (∑ k ∈ Finset.range (n + 1),
        p ^ k * (1 - p) ^ (n - k) * ((n.choose k : ℕ) : ℝ))
          = (p + (1 - p)) ^ n := by
              simpa [mul_assoc, mul_comm, mul_left_comm] using h.symm
      _ = 1 := by ring
  simpa [mul_assoc, mul_comm, mul_left_comm] using hsum

lemma binomCardMoment_nonneg {n q : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binomCardMoment n q p := by
  unfold binomCardMoment
  refine Finset.sum_nonneg ?_
  intro k hk
  have h1mp : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
      (pow_nonneg h1mp _))
    (pow_nonneg (Nat.cast_nonneg _) _)

lemma one_add_two_mul_pow_le_two_mul_pow {q : ℕ} {x : ℝ}
    (hx0 : 0 ≤ x) (hxq : (q : ℝ) ≤ x) :
    (1 + 2 * x) ^ q ≤ 2 * (2 * x) ^ q := by
  have hx2 : 0 ≤ 2 * x := by positivity
  have hterm :
      ∀ i ∈ Finset.range (q + 1),
        1 ^ i * (2 * x) ^ (q - i) * ((q.choose i : ℕ) : ℝ)
          ≤ (2 * x) ^ q * ((1 / 2 : ℝ) ^ i) := by
    intro i hi
    have hiq : i ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hchoose_nat : q.choose i ≤ q ^ i := Nat.choose_le_pow q i
    have hchoose : (((q.choose i : ℕ) : ℝ)) ≤ (x : ℝ) ^ i := by
      calc
        (((q.choose i : ℕ) : ℝ)) ≤ (q : ℝ) ^ i := by
          exact_mod_cast hchoose_nat
        _ ≤ x ^ i := pow_le_pow_left₀ (Nat.cast_nonneg q) hxq i
    have hpow :
        x ^ i * (2 * x) ^ (q - i) = (2 * x) ^ q * ((1 / 2 : ℝ) ^ i) := by
      have hhalf : (2 * x) ^ i * ((1 / 2 : ℝ) ^ i) = x ^ i := by
        rw [← mul_pow]
        ring_nf
      calc
        x ^ i * (2 * x) ^ (q - i)
            = ((2 * x) ^ i * ((1 / 2 : ℝ) ^ i)) * (2 * x) ^ (q - i) := by
                rw [hhalf]
        _ = ((2 * x) ^ i * (2 * x) ^ (q - i)) * ((1 / 2 : ℝ) ^ i) := by
                ring
        _ = (2 * x) ^ q * ((1 / 2 : ℝ) ^ i) := by
                rw [← pow_add, Nat.add_sub_of_le hiq]
    calc
      1 ^ i * (2 * x) ^ (q - i) * (((q.choose i : ℕ) : ℝ))
          = (((q.choose i : ℕ) : ℝ)) * (2 * x) ^ (q - i) := by ring
      _ ≤ x ^ i * (2 * x) ^ (q - i) := by
        exact mul_le_mul_of_nonneg_right hchoose (pow_nonneg hx2 _)
      _ = (2 * x) ^ q * ((1 / 2 : ℝ) ^ i) := hpow
  calc
    (1 + 2 * x) ^ q
        = ∑ i ∈ Finset.range (q + 1),
            1 ^ i * (2 * x) ^ (q - i) * ((q.choose i : ℕ) : ℝ) := by
              simpa [mul_assoc, mul_comm, mul_left_comm] using add_pow (1 : ℝ) (2 * x) q
    _ ≤ ∑ i ∈ Finset.range (q + 1), (2 * x) ^ q * ((1 / 2 : ℝ) ^ i) :=
        Finset.sum_le_sum hterm
    _ = (2 * x) ^ q * (∑ i ∈ Finset.range (q + 1), ((1 / 2 : ℝ) ^ i)) := by
        exact (Finset.mul_sum (Finset.range (q+1)) (fun i => ((1/2:ℝ)^i)) ((2*x)^q)).symm
    _ ≤ (2 * x) ^ q * 2 := by
      have hgeom :
          (∑ i ∈ Finset.range (q + 1), ((1 / 2 : ℝ) ^ i)) ≤ 2 := by
        have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ (q + 1) := by positivity
        rw [geom_sum_eq (show (1 / 2 : ℝ) ≠ 1 by norm_num)]
        rw [div_le_iff_of_neg (by norm_num)]
        nlinarith [hpow_nonneg]
      exact mul_le_mul_of_nonneg_left hgeom (pow_nonneg hx2 _)
    _ = 2 * (2 * x) ^ q := by ring

lemma binomCardMoment_succ_eq (n q : ℕ) (p : ℝ) :
    binomCardMoment (n + 1) (q + 1) p =
      ((n + 1 : ℕ) : ℝ) * p *
        (∑ r ∈ Finset.range (q + 1),
          (((q.choose r : ℕ) : ℝ) * binomCardMoment n r p)) := by
  unfold binomCardMoment
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_pow (Nat.succ_ne_zero q), mul_zero, add_zero]
  have hshift :
      (∑ k ∈ Finset.range (n + 1),
          (((n + 1).choose (k + 1) : ℕ) : ℝ) *
            p ^ (k + 1) * (1 - p) ^ (n + 1 - (k + 1)) *
              ((k + 1 : ℕ) : ℝ) ^ (q + 1))
        =
      ((n + 1 : ℕ) : ℝ) * p *
        (∑ k ∈ Finset.range (n + 1),
          (((n.choose k : ℕ) : ℝ) *
            p ^ k * (1 - p) ^ (n - k) * (((k : ℕ) : ℝ) + 1) ^ q)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hsub : n + 1 - (k + 1) = n - k := Nat.succ_sub_succ_eq_sub n k
    have hchoose :
        (((n + 1).choose (k + 1) : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) =
          ((n + 1 : ℕ) : ℝ) * (((n.choose k : ℕ) : ℝ)) := by
      have hnat := Nat.add_one_mul_choose_eq n k
      exact_mod_cast hnat.symm
    calc
      (((n + 1).choose (k + 1) : ℕ) : ℝ) *
            p ^ (k + 1) * (1 - p) ^ (n + 1 - (k + 1)) *
              ((k + 1 : ℕ) : ℝ) ^ (q + 1)
          = (((n + 1).choose (k + 1) : ℕ) : ℝ) *
              ((k + 1 : ℕ) : ℝ) *
              p * p ^ k * (1 - p) ^ (n - k) *
              (((k : ℕ) : ℝ) + 1) ^ q := by
              rw [hsub, pow_succ' p k, pow_succ]
              norm_num
              ring
      _ = (((n + 1 : ℕ) : ℝ) * (((n.choose k : ℕ) : ℝ))) *
              p * p ^ k * (1 - p) ^ (n - k) *
              (((k : ℕ) : ℝ) + 1) ^ q := by rw [hchoose]
      _ = ((n + 1 : ℕ) : ℝ) * p *
            ((((n.choose k : ℕ) : ℝ) * p ^ k * (1 - p) ^ (n - k) *
              (((k : ℕ) : ℝ) + 1) ^ q)) := by ring
  have hswap :
      (∑ k ∈ Finset.range (n + 1),
          (((n.choose k : ℕ) : ℝ) *
            p ^ k * (1 - p) ^ (n - k) * (((k : ℕ) : ℝ) + 1) ^ q))
        =
      ∑ r ∈ Finset.range (q + 1),
        (((q.choose r : ℕ) : ℝ) *
          ∑ k ∈ Finset.range (n + 1),
            (((n.choose k : ℕ) : ℝ) *
              p ^ k * (1 - p) ^ (n - k) * (k : ℝ) ^ r)) := by
    have hexpand : ∀ k : ℕ, (((k : ℕ) : ℝ) + 1) ^ q
        = ∑ r ∈ Finset.range (q + 1), (k : ℝ) ^ r * ((q.choose r : ℕ) : ℝ) := by
      intro k
      have := add_pow ((k : ℝ)) (1 : ℝ) q
      simpa [one_pow, mul_one] using this
    calc
      (∑ k ∈ Finset.range (n + 1),
          (((n.choose k : ℕ) : ℝ) * p ^ k * (1 - p) ^ (n - k) * (((k : ℕ) : ℝ) + 1) ^ q))
          = ∑ k ∈ Finset.range (n + 1),
              ∑ r ∈ Finset.range (q + 1),
                (((n.choose k : ℕ) : ℝ) * p ^ k * (1 - p) ^ (n - k)
                  * ((k : ℝ) ^ r * ((q.choose r : ℕ) : ℝ))) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [hexpand k, Finset.mul_sum]
      _ = ∑ r ∈ Finset.range (q + 1),
            ∑ k ∈ Finset.range (n + 1),
                (((n.choose k : ℕ) : ℝ) * p ^ k * (1 - p) ^ (n - k)
                  * ((k : ℝ) ^ r * ((q.choose r : ℕ) : ℝ))) := Finset.sum_comm
      _ = ∑ r ∈ Finset.range (q + 1),
            (((q.choose r : ℕ) : ℝ) *
              ∑ k ∈ Finset.range (n + 1),
                (((n.choose k : ℕ) : ℝ) * p ^ k * (1 - p) ^ (n - k) * (k : ℝ) ^ r)) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            rw [Finset.mul_sum (Finset.range (n + 1))
              (fun k =>
                (((n.choose k : ℕ) : ℝ) * p ^ k * (1 - p) ^ (n - k) * (k : ℝ) ^ r))
              (((q.choose r : ℕ) : ℝ))]
            refine Finset.sum_congr rfl ?_
            intro k hk
            ring
  rw [hshift, hswap]

theorem binomCardMoment_le_two_mul_scale_pow
    (n q : ℕ) (p x : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hx1 : 1 ≤ x) (hnpx : (n : ℝ) * p ≤ x) (hqx : (q : ℝ) ≤ x) :
    binomCardMoment n q p ≤ (2 * x) ^ q := by
  revert n x
  refine Nat.strong_induction_on q ?_
  intro q ih n x hx1 hnpx hqx
  cases q with
  | zero =>
      simp [binomCardMoment_zero]
  | succ q =>
      cases n with
      | zero =>
          have hx0 : 0 ≤ x := le_trans zero_le_one hx1
          unfold binomCardMoment
          simp [pow_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx0)]
      | succ n =>
          have hx0 : 0 ≤ x := le_trans zero_le_one hx1
          have hq_le_x : (q : ℝ) ≤ x := by
            exact (Nat.cast_le.mpr (Nat.le_succ q)).trans hqx
          have hscale_n : (n : ℝ) * p ≤ x := by
            have hnle : (n : ℝ) ≤ (n + 1 : ℕ) := by norm_num
            have hp0' : 0 ≤ p := hp0
            calc
              (n : ℝ) * p ≤ ((n + 1 : ℕ) : ℝ) * p :=
                mul_le_mul_of_nonneg_right hnle hp0'
              _ ≤ x := hnpx
          have hsum_nonneg :
              0 ≤ ∑ r ∈ Finset.range (q + 1),
                (((q.choose r : ℕ) : ℝ) * binomCardMoment n r p) := by
            refine Finset.sum_nonneg ?_
            intro r hr
            exact mul_nonneg (Nat.cast_nonneg _)
              (binomCardMoment_nonneg (n := n) (q := r) hp0 hp1)
          have hsum_le :
              (∑ r ∈ Finset.range (q + 1),
                (((q.choose r : ℕ) : ℝ) * binomCardMoment n r p))
                ≤ ∑ r ∈ Finset.range (q + 1),
                    (((q.choose r : ℕ) : ℝ) * (2 * x) ^ r) := by
            refine Finset.sum_le_sum ?_
            intro r hr
            have hrq : r ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
            have hrx : (r : ℝ) ≤ x := by
              exact (Nat.cast_le.mpr hrq).trans hq_le_x
            have hrlt : r < q + 1 := Finset.mem_range.mp hr
            have hrec := ih r hrlt n x hx1 hscale_n hrx
            exact mul_le_mul_of_nonneg_left hrec (by positivity)
          have hsum_eval :
              (∑ r ∈ Finset.range (q + 1),
                    (((q.choose r : ℕ) : ℝ) * (2 * x) ^ r))
                = (1 + 2 * x) ^ q := by
            simpa [mul_assoc, mul_comm, mul_left_comm, add_comm] using
              (add_pow (2 * x) (1 : ℝ) q).symm
          calc
            binomCardMoment (n + 1) (q + 1) p
                = ((n + 1 : ℕ) : ℝ) * p *
                    (∑ r ∈ Finset.range (q + 1),
                      (((q.choose r : ℕ) : ℝ) * binomCardMoment n r p)) := by
                    rw [binomCardMoment_succ_eq]
            _ ≤ x *
                    (∑ r ∈ Finset.range (q + 1),
                      (((q.choose r : ℕ) : ℝ) * binomCardMoment n r p)) := by
                    exact mul_le_mul_of_nonneg_right hnpx hsum_nonneg
            _ ≤ x *
                    (∑ r ∈ Finset.range (q + 1),
                      (((q.choose r : ℕ) : ℝ) * (2 * x) ^ r)) := by
                    exact mul_le_mul_of_nonneg_left hsum_le hx0
            _ = x * (1 + 2 * x) ^ q := by rw [hsum_eval]
            _ ≤ x * (2 * (2 * x) ^ q) := by
                    exact mul_le_mul_of_nonneg_left
                      (one_add_two_mul_pow_le_two_mul_pow hx0 hq_le_x) hx0
            _ = (2 * x) ^ (q + 1) := by ring

/-- Relaxed Lemma 6.2 with scale `x := 2·(n·p)`: valid up to `q ≤ 2·n·p`. -/
theorem rowBernoulliMoment_le_four_np_pow
    (n q : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq2np : (q : ℝ) ≤ 2 * ((n : ℝ) * p))
    (h1 : 1 ≤ 2 * ((n : ℝ) * p)) :
    rowBernoulliMoment n q p ≤ (4 * ((n : ℝ) * p)) ^ q := by
  rw [rowBernoulliMoment_eq_binomCardMoment]
  have hx1 : 1 ≤ 2 * ((n : ℝ) * p) := h1
  have hnpx : (n : ℝ) * p ≤ 2 * ((n : ℝ) * p) := by nlinarith [mul_nonneg (Nat.cast_nonneg n) hp0]
  have := binomCardMoment_le_two_mul_scale_pow n q p (2 * ((n : ℝ) * p)) hp0 hp1 hx1 hnpx hq2np
  calc binomCardMoment n q p ≤ (2 * (2 * ((n : ℝ) * p))) ^ q := this
    _ = (4 * ((n : ℝ) * p)) ^ q := by ring_nf

end CR2008Lemma62

/-! ## Brick 2 : marginalization (single-row q-moment) -/

namespace Marginal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma weight_eq_prod (p : ℝ) (Omega : Finset ι) :
    p ^ Omega.card * (1 - p) ^ (Fintype.card ι - Omega.card)
      = ∏ c : ι, (if c ∈ Omega then p else (1 - p)) := by
  classical
  have hsplit :
      (∏ c : ι, (if c ∈ Omega then p else (1 - p)))
        = (∏ c ∈ Omega, p) * (∏ c ∈ (Finset.univ \ Omega), (1 - p)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun c => c ∈ Omega)]
    congr 1
    · apply Finset.prod_congr
      · ext c; simp
      · intro c hc
        have hc' : c ∈ Omega := by simpa using hc
        simp [hc']
    · apply Finset.prod_congr
      · ext c; simp
      · intro c hc
        have hc' : c ∉ Omega := by simpa using hc
        simp [hc']
  rw [hsplit]
  rw [Finset.prod_const, Finset.prod_const]
  have hc : (Finset.univ \ Omega).card = Fintype.card ι - Omega.card := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]
  rw [hc]

lemma sum_powerset_split (A : Finset ι) (F : Finset ι → ℝ) :
    (∑ Omega : Finset ι, F Omega)
      = ∑ Sa ∈ A.powerset, ∑ Sr ∈ Aᶜ.powerset, F (Sa ∪ Sr) := by
  classical
  rw [Finset.sum_sigma']
  apply Finset.sum_nbij' (i := fun Omega => ⟨Omega ∩ A, Omega ∩ Aᶜ⟩)
    (j := fun x => x.1 ∪ x.2)
  · intro Omega _
    simp only [Finset.mem_sigma, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
  · intro x hx
    exact Finset.mem_univ _
  · intro Omega _
    rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hx
    obtain ⟨hSa, hSr⟩ := hx
    have hSadisj : Disjoint x.1 Aᶜ := Disjoint.mono_left hSa disjoint_compl_right
    have hSrdisj : Disjoint x.2 A := Disjoint.mono_left hSr disjoint_compl_left
    ext
    · simp only [Finset.union_inter_distrib_right]
      rw [Finset.inter_eq_left.mpr hSa, (Finset.disjoint_iff_inter_eq_empty.mp hSrdisj)]
      simp
    · simp only [Finset.union_inter_distrib_right]
      rw [Finset.inter_eq_left.mpr hSr, (Finset.disjoint_iff_inter_eq_empty.mp hSadisj)]
      simp
  · intro Omega _
    congr 1
    rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]

lemma rest_sum_one (p : ℝ) (B : Finset ι) :
    (∑ Sr ∈ B.powerset, ∏ c ∈ B, (if c ∈ Sr then p else (1 - p))) = 1 := by
  classical
  have key : ∀ Sr ∈ B.powerset,
      (∏ c ∈ B, (if c ∈ Sr then p else (1 - p)))
        = (∏ c ∈ Sr, p) * ∏ c ∈ B \ Sr, (1 - p) := by
    intro Sr hSr
    rw [Finset.mem_powerset] at hSr
    classical
    rw [← Finset.prod_filter_mul_prod_filter_not B (fun c => c ∈ Sr)]
    congr 1
    · refine Finset.prod_congr ?_ (fun c hc => ?_)
      · ext c; simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hSr h, h⟩⟩
      · rw [if_pos hc]
    · refine Finset.prod_congr ?_ (fun c hc => ?_)
      · ext c; simp only [Finset.mem_filter, Finset.mem_sdiff, and_comm]
      · rw [Finset.mem_sdiff] at hc; rw [if_neg hc.2]
  rw [Finset.sum_congr rfl key]
  rw [← Finset.prod_add]
  apply Finset.prod_eq_one
  intro c _; ring

noncomputable def rowCount {n1 n2 : ℕ} (Omega : Finset (Fin n1 × Fin n2)) (a : Fin n1) : ℕ :=
  (Finset.univ.filter (fun b : Fin n2 => (a, b) ∈ Omega)).card

noncomputable def bExp2 {n1 n2 : ℕ} (p : ℝ) (F : Finset (Fin n1 × Fin n2) → ℝ) : ℝ :=
  ∑ Omega : Finset (Fin n1 × Fin n2),
    p ^ Omega.card * (1 - p) ^ (Fintype.card (Fin n1 × Fin n2) - Omega.card) * F Omega

noncomputable def rowBern (n q : ℕ) (p : ℝ) : ℝ :=
  ∑ S : Finset (Fin n), p ^ S.card * (1 - p) ^ (n - S.card) * (S.card : ℝ) ^ q

def rowCells {n1 n2 : ℕ} (a : Fin n1) : Finset (Fin n1 × Fin n2) :=
  Finset.univ.filter (fun c => c.1 = a)

lemma rowCount_union {n1 n2 : ℕ} (a : Fin n1)
    {Sa Sr : Finset (Fin n1 × Fin n2)} (hSa : Sa ⊆ rowCells a) (hSr : Sr ⊆ (rowCells a)ᶜ) :
    rowCount (Sa ∪ Sr) a = Sa.card := by
  classical
  unfold rowCount
  refine Finset.card_nbij' (i := fun b : Fin n2 => ((a, b) : Fin n1 × Fin n2))
    (j := fun c : Fin n1 × Fin n2 => c.2) ?_ ?_ ?_ ?_
  · intro b hb
    rw [Finset.mem_coe, Finset.mem_filter] at hb
    rw [Finset.mem_coe]
    rcases Finset.mem_union.mp hb.2 with hb' | hb'
    · exact hb'
    · exfalso
      have hmem := hSr hb'
      rw [Finset.mem_compl, rowCells, Finset.mem_filter] at hmem
      exact hmem ⟨Finset.mem_univ _, rfl⟩
  · intro c hc
    rw [Finset.mem_coe] at hc
    have hc1 : c.1 = a := by
      have := hSa hc
      simp only [rowCells, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Finset.mem_union.mpr; left
    have : (a, c.2) = c := by rw [← hc1]
    rw [this]; exact hc
  · intro b _; rfl
  · intro c hc
    rw [Finset.mem_coe] at hc
    have hc1 : c.1 = a := by
      have := hSa hc
      simp only [rowCells, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    show (a, c.2) = c
    rw [← hc1]

lemma card_rowCells {n1 n2 : ℕ} (a : Fin n1) :
    (rowCells (n2 := n2) a).card = n2 := by
  classical
  have : (rowCells (n2 := n2) a).card = (Finset.univ : Finset (Fin n2)).card := by
    apply Finset.card_nbij' (i := fun c : Fin n1 × Fin n2 => c.2)
      (j := fun b : Fin n2 => ((a, b) : Fin n1 × Fin n2))
    · intro c _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro b _
      rw [Finset.mem_coe, rowCells, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, rfl⟩
    · intro c hc
      rw [Finset.mem_coe, rowCells, Finset.mem_filter] at hc
      show (a, c.2) = c
      rw [← hc.2]
    · intro b _; rfl
  rw [this, Finset.card_univ, Fintype.card_fin]

lemma snd_pair_inj {n1 n2 : ℕ} (a : Fin n1) :
    Function.Injective (fun b : Fin n2 => ((a, b) : Fin n1 × Fin n2)) := by
  intro b1 b2 h; simpa using h

lemma image_pair_card {n1 n2 : ℕ} (a : Fin n1) (S : Finset (Fin n2)) :
    (S.image (fun b => ((a, b) : Fin n1 × Fin n2))).card = S.card :=
  Finset.card_image_of_injective S (snd_pair_inj a)

lemma prod_rowCells_image {n1 n2 : ℕ} (p : ℝ) (a : Fin n1) (S : Finset (Fin n2)) :
    (∏ c ∈ rowCells (n2 := n2) a,
        (if c ∈ S.image (fun b => ((a, b) : Fin n1 × Fin n2)) then p else (1 - p)))
      = p ^ S.card * (1 - p) ^ (n2 - S.card) := by
  classical
  rw [show (∏ c ∈ rowCells (n2 := n2) a,
        (if c ∈ S.image (fun b => ((a, b) : Fin n1 × Fin n2)) then p else (1 - p)))
        = ∏ b : Fin n2, (if b ∈ S then p else (1 - p)) from ?_]
  · have := weight_eq_prod (ι := Fin n2) p S
    rw [Fintype.card_fin] at this
    exact this.symm
  · apply Finset.prod_nbij' (i := fun c : Fin n1 × Fin n2 => c.2)
      (j := fun b : Fin n2 => ((a, b) : Fin n1 × Fin n2))
    · intro c _; exact Finset.mem_univ _
    · intro b _
      rw [rowCells, Finset.mem_filter]; exact ⟨Finset.mem_univ _, rfl⟩
    · intro c hc
      rw [rowCells, Finset.mem_filter] at hc
      show (a, c.2) = c; rw [← hc.2]
    · intro b _; rfl
    · intro c hc
      rw [rowCells, Finset.mem_filter] at hc
      congr 1
      apply propext
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨b, hb, hbc⟩
        have : b = c.2 := by rw [← hbc]
        rw [← this]; exact hb
      · intro hc2
        exact ⟨c.2, hc2, by show (a, c.2) = c; rw [← hc.2]⟩

theorem bExp2_rowCount_pow_eq_rowBern {n1 n2 : ℕ} (p : ℝ) (a : Fin n1) (q : ℕ) :
    bExp2 (n1 := n1) (n2 := n2) p (fun Omega => (rowCount Omega a : ℝ) ^ q) = rowBern n2 q p := by
  classical
  unfold bExp2
  have hstep1 : ∀ Omega : Finset (Fin n1 × Fin n2),
      p ^ Omega.card * (1 - p) ^ (Fintype.card (Fin n1 × Fin n2) - Omega.card)
          * (rowCount Omega a : ℝ) ^ q
        = (∏ c : Fin n1 × Fin n2, (if c ∈ Omega then p else (1 - p))) * (rowCount Omega a : ℝ) ^ q := by
    intro Omega; rw [weight_eq_prod]
  rw [Finset.sum_congr rfl (fun Omega _ => hstep1 Omega)]
  rw [sum_powerset_split (rowCells a)
      (fun Omega => (∏ c : Fin n1 × Fin n2, (if c ∈ Omega then p else (1 - p)))
        * (rowCount Omega a : ℝ) ^ q)]
  have hinner : ∀ Sa ∈ (rowCells a).powerset, ∀ Sr ∈ (rowCells a)ᶜ.powerset,
      (∏ c : Fin n1 × Fin n2, (if c ∈ (Sa ∪ Sr) then p else (1 - p)))
          * (rowCount (Sa ∪ Sr) a : ℝ) ^ q
        = ((∏ c ∈ rowCells a, (if c ∈ Sa then p else (1 - p))) * (Sa.card : ℝ) ^ q)
            * (∏ c ∈ (rowCells a)ᶜ, (if c ∈ Sr then p else (1 - p))) := by
    intro Sa hSa Sr hSr
    rw [Finset.mem_powerset] at hSa hSr
    have hsplitprod :
        (∏ c : Fin n1 × Fin n2, (if c ∈ (Sa ∪ Sr) then p else (1 - p)))
          = (∏ c ∈ rowCells a, (if c ∈ (Sa ∪ Sr) then p else (1 - p)))
            * (∏ c ∈ (rowCells a)ᶜ, (if c ∈ (Sa ∪ Sr) then p else (1 - p))) := by
      rw [← Finset.prod_mul_prod_compl (rowCells a)
            (fun c => (if c ∈ (Sa ∪ Sr) then p else (1 - p)))]
    rw [hsplitprod, rowCount_union a hSa hSr]
    have hOnRow : (∏ c ∈ rowCells a, (if c ∈ (Sa ∪ Sr) then p else (1 - p)))
        = (∏ c ∈ rowCells a, (if c ∈ Sa then p else (1 - p))) := by
      refine Finset.prod_congr rfl (fun c hc => ?_)
      have hcsr : c ∉ Sr := fun h => (Finset.mem_compl.mp (hSr h)) hc
      by_cases hcsa : c ∈ Sa
      · rw [if_pos (Finset.mem_union.mpr (Or.inl hcsa)), if_pos hcsa]
      · rw [if_neg (by simp [Finset.mem_union, hcsa, hcsr]), if_neg hcsa]
    have hOnComp : (∏ c ∈ (rowCells a)ᶜ, (if c ∈ (Sa ∪ Sr) then p else (1 - p)))
        = (∏ c ∈ (rowCells a)ᶜ, (if c ∈ Sr then p else (1 - p))) := by
      refine Finset.prod_congr rfl (fun c hc => ?_)
      have hcsa : c ∉ Sa := fun h => (Finset.mem_compl.mp hc) (hSa h)
      by_cases hcsr : c ∈ Sr
      · rw [if_pos (Finset.mem_union.mpr (Or.inr hcsr)), if_pos hcsr]
      · rw [if_neg (by simp [Finset.mem_union, hcsa, hcsr]), if_neg hcsr]
    rw [hOnRow, hOnComp]; ring
  rw [Finset.sum_congr rfl (fun Sa hSa => Finset.sum_congr rfl (fun Sr hSr => hinner Sa hSa Sr hSr))]
  have hfactor : ∀ Sa ∈ (rowCells (n2 := n2) a).powerset,
      (∑ Sr ∈ (rowCells (n2 := n2) a)ᶜ.powerset,
        ((∏ c ∈ rowCells (n2 := n2) a, (if c ∈ Sa then p else (1 - p))) * (Sa.card : ℝ) ^ q)
          * (∏ c ∈ (rowCells (n2 := n2) a)ᶜ, (if c ∈ Sr then p else (1 - p))))
        = (∏ c ∈ rowCells (n2 := n2) a, (if c ∈ Sa then p else (1 - p))) * (Sa.card : ℝ) ^ q := by
    intro Sa _
    have hrest := rest_sum_one (ι := Fin n1 × Fin n2) p ((rowCells a)ᶜ)
    rw [← Finset.mul_sum, hrest, mul_one]
  rw [Finset.sum_congr rfl hfactor]
  unfold rowBern
  refine (Finset.sum_nbij' (i := fun S : Finset (Fin n2) => S.image (fun b => ((a, b) : Fin n1 × Fin n2)))
    (j := fun Sa : Finset (Fin n1 × Fin n2) => Sa.image (fun c => c.2)) ?_ ?_ ?_ ?_ ?_).symm
  · intro S hS
    rw [Finset.mem_powerset]
    intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨b, _, hbc⟩ := hc
    rw [rowCells, Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [← hbc]⟩
  · intro Sa _; exact Finset.mem_univ _
  · intro S _
    try dsimp only
    rw [Finset.image_image]
    simp
  · intro Sa hSa
    rw [Finset.mem_powerset] at hSa
    try dsimp only
    rw [Finset.image_image]
    rw [Finset.image_congr (g := fun c : Fin n1 × Fin n2 => c) ?_, Finset.image_id']
    intro c hc
    have := hSa hc
    rw [rowCells, Finset.mem_filter] at this
    show (a, c.2) = c; rw [← this.2]
  · intro S _
    rw [prod_rowCells_image p a S, image_pair_card a S]

end Marginal

/-! ## Brick 3 : max-over-rows moment -/

namespace CR2008Lemma62Max

noncomputable def rowCount {n1 n2 : ℕ} (Omega : Finset (Fin n1 × Fin n2)) (a : Fin n1) : ℕ :=
  (Finset.univ.filter (fun b : Fin n2 => (a, b) ∈ Omega)).card

noncomputable def bExp {n1 n2 : ℕ} (p : ℝ) (F : Finset (Fin n1 × Fin n2) → ℝ) : ℝ :=
  ∑ Omega : Finset (Fin n1 × Fin n2),
    p ^ Omega.card * (1 - p) ^ (Fintype.card (Fin n1 × Fin n2) - Omega.card) * F Omega

lemma max_pow_le_sum_pow {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (q : ℕ) :
    (⨆ i, f i) ^ q ≤ ∑ i, (f i) ^ q := by
  classical
  obtain ⟨a, ha⟩ := Finite.exists_max f
  have hsup : (⨆ i, f i) = f a := by
    apply le_antisymm
    · apply ciSup_le; intro i; exact ha i
    · exact le_ciSup (Finite.bddAbove_range f) a
  rw [hsup]
  calc (f a) ^ q ≤ ∑ i, (f i) ^ q := by
        refine Finset.single_le_sum (f := fun i => (f i) ^ q) ?_ (Finset.mem_univ a)
        intro i _; exact pow_nonneg (hf i) q

lemma bExp_sum {n1 n2 : ℕ} (p : ℝ) {κ : Type*} (s : Finset κ)
    (F : κ → Finset (Fin n1 × Fin n2) → ℝ) :
    bExp p (fun Omega => ∑ a ∈ s, F a Omega) = ∑ a ∈ s, bExp p (fun Omega => F a Omega) := by
  classical
  unfold bExp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Omega _
  rw [Finset.mul_sum]

lemma bExp_mono {n1 n2 : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {F G : Finset (Fin n1 × Fin n2) → ℝ} (h : ∀ Omega, F Omega ≤ G Omega) :
    bExp p F ≤ bExp p G := by
  classical
  unfold bExp
  apply Finset.sum_le_sum
  intro Omega _
  have hw : 0 ≤ p ^ Omega.card * (1 - p) ^ (Fintype.card (Fin n1 × Fin n2) - Omega.card) := by
    apply mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  exact mul_le_mul_of_nonneg_left (h Omega) hw

lemma bExp_add {n1 n2 : ℕ} (p : ℝ) (F G : Finset (Fin n1 × Fin n2) → ℝ) :
    bExp p (fun Omega => F Omega + G Omega) = bExp p F + bExp p G := by
  unfold bExp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Omega _; ring

lemma bExp_smul {n1 n2 : ℕ} (p c : ℝ) (F : Finset (Fin n1 × Fin n2) → ℝ) :
    bExp p (fun Omega => c * F Omega) = c * bExp p F := by
  unfold bExp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Omega _; ring

theorem bExp_max_rowCount_pow_le {n1 n2 : ℕ} [Nonempty (Fin n1)] {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (q : ℕ)
    (B : ℝ)
    (hrow : ∀ a : Fin n1,
      bExp p (fun Omega : Finset (Fin n1 × Fin n2) => (rowCount Omega a : ℝ) ^ q) ≤ B) :
    bExp p (fun Omega : Finset (Fin n1 × Fin n2) => (⨆ a : Fin n1, (rowCount Omega a : ℝ)) ^ q)
      ≤ (n1 : ℝ) * B := by
  classical
  have hpt : ∀ Omega : Finset (Fin n1 × Fin n2),
      (⨆ a : Fin n1, (rowCount Omega a : ℝ)) ^ q
        ≤ ∑ a : Fin n1, ((rowCount Omega a : ℝ)) ^ q :=
    fun Omega => max_pow_le_sum_pow (fun a => (rowCount Omega a : ℝ)) (fun a => by positivity) q
  calc bExp p (fun Omega : Finset (Fin n1 × Fin n2) => (⨆ a : Fin n1, (rowCount Omega a : ℝ)) ^ q)
      ≤ bExp p (fun Omega : Finset (Fin n1 × Fin n2) => ∑ a : Fin n1, ((rowCount Omega a : ℝ)) ^ q) :=
        bExp_mono hp0 hp1 hpt
    _ = ∑ a : Fin n1, bExp p (fun Omega : Finset (Fin n1 × Fin n2) => ((rowCount Omega a : ℝ)) ^ q) :=
        bExp_sum (n1 := n1) (n2 := n2) p Finset.univ
          (fun a Omega => ((rowCount Omega a : ℝ)) ^ q)
    _ ≤ ∑ _a : Fin n1, B := Finset.sum_le_sum (fun a _ => hrow a)
    _ = (n1 : ℝ) * B := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end CR2008Lemma62Max

/-! ## Assembly -/

namespace Sol2pNctrl

open MatrixCompletion
open scoped Classical BigOperators

/-- The platform `bernoulliExpectation` is the inlined `bExp`. -/
lemma bernoulliExpectation_eq_bExp {n1 n2 : ℕ} (p : ℝ)
    (F : Finset (Fin n1 × Fin n2) → ℝ) :
    bernoulliExpectation p F = CR2008Lemma62Max.bExp p F := by
  unfold bernoulliExpectation CR2008Lemma62Max.bExp bernoulliObservationWeight
  rfl

/-- `∑_j 1[(i,j)∈Ω]` equals the `rowCount`. -/
lemma sum_indicator_eq_rowCount {n1 n2 : ℕ}
    (Omega : Finset (Fin n1 × Fin n2)) (i : Fin n1) :
    (∑ j : Fin n2, if (i, j) ∈ Omega then (1 : ℝ) else 0)
      = (CR2008Lemma62Max.rowCount Omega i : ℝ) := by
  classical
  unfold CR2008Lemma62Max.rowCount
  rw [Finset.sum_boole]

/-- `sampledRowCountMax` equals `⨆ i, rowCount`. -/
lemma sampledRowCountMax_eq_iSup {n1 n2 : ℕ}
    (Omega : Finset (Fin n1 × Fin n2)) :
    sampledRowCountMax Omega
      = ⨆ i : Fin n1, (CR2008Lemma62Max.rowCount Omega i : ℝ) := by
  unfold sampledRowCountMax
  congr 1
  ext i
  exact sum_indicator_eq_rowCount Omega i

/-- Inlined row energy↔count bridge. -/
lemma sampledRowEnergyMax_le {n1 n2 : ℕ}
    (Omega : Finset (Fin n1 × Fin n2)) (X : Matrix (Fin n1) (Fin n2) ℝ) :
    sampledRowEnergyMax Omega X ≤ entrySupNorm X ^ 2 * sampledRowCountMax Omega := by
  by_cases h₁ : IsEmpty (Fin n1)
  · haveI := h₁
    simp [sampledRowEnergyMax, sampledRowCountMax]
  · by_cases h₂ : IsEmpty (Fin n2)
    · haveI := h₂
      simp [sampledRowEnergyMax, sampledRowCountMax]
    · have hn₁ : Nonempty (Fin n1) := not_isEmpty_iff.mp h₁
      have hn₂ : Nonempty (Fin n2) := not_isEmpty_iff.mp h₂
      have hentry_nonneg : 0 ≤ entrySupNorm X := by
        rcases hn₁ with ⟨i0⟩
        rcases hn₂ with ⟨j0⟩
        exact le_trans (abs_nonneg (X i0 j0))
          (le_trans
            (le_ciSup (Finite.bddAbove_range (fun j : Fin n2 => |X i0 j|)) j0)
            (le_ciSup
              (Finite.bddAbove_range (fun i : Fin n1 => ⨆ j : Fin n2, |X i j|)) i0))
      unfold sampledRowEnergyMax
      apply ciSup_le
      intro i
      unfold sampledRowCountMax
      have hrow :
          (∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0) ≤
            entrySupNorm X ^ 2 *
              (∑ j : Fin n2, if (i, j) ∈ Omega then (1 : ℝ) else 0) := by
        calc
          (∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0)
              ≤ ∑ j : Fin n2, if (i, j) ∈ Omega then entrySupNorm X ^ 2 else 0 := by
                apply Finset.sum_le_sum
                intro j _hj
                by_cases hmem : (i, j) ∈ Omega
                · simp [hmem]
                  have hij_abs : |X i j| ≤ entrySupNorm X := by
                    exact le_trans
                      (le_ciSup (Finite.bddAbove_range (fun j : Fin n2 => |X i j|)) j)
                      (le_ciSup
                        (Finite.bddAbove_range
                          (fun i : Fin n1 => ⨆ j : Fin n2, |X i j|)) i)
                  rw [← sq_abs (X i j)]
                  exact sq_le_sq'
                    (le_trans (neg_nonpos.mpr hentry_nonneg) (abs_nonneg (X i j))) hij_abs
                · simp [hmem]
          _ = entrySupNorm X ^ 2 *
              (∑ j : Fin n2, if (i, j) ∈ Omega then (1 : ℝ) else 0) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _hj
                by_cases hmem : (i, j) ∈ Omega
                · simp [hmem]
                · simp [hmem]
      exact le_trans hrow
        (mul_le_mul_of_nonneg_left
          (le_ciSup
            (Finite.bddAbove_range
              (fun i : Fin n1 =>
                ∑ j : Fin n2, if (i, j) ∈ Omega then (1 : ℝ) else 0)) i)
          (sq_nonneg (entrySupNorm X)))

/-- Inlined column energy↔count bridge. -/
lemma sampledColumnEnergyMax_le {n1 n2 : ℕ}
    (Omega : Finset (Fin n1 × Fin n2)) (X : Matrix (Fin n1) (Fin n2) ℝ) :
    sampledColumnEnergyMax Omega X ≤ entrySupNorm X ^ 2 * sampledColumnCountMax Omega := by
  by_cases h₁ : IsEmpty (Fin n1)
  · haveI := h₁
    simp [sampledColumnEnergyMax, sampledColumnCountMax]
  · by_cases h₂ : IsEmpty (Fin n2)
    · haveI := h₂
      simp [sampledColumnEnergyMax, sampledColumnCountMax]
    · have hn₁ : Nonempty (Fin n1) := not_isEmpty_iff.mp h₁
      have hn₂ : Nonempty (Fin n2) := not_isEmpty_iff.mp h₂
      have hentry_nonneg : 0 ≤ entrySupNorm X := by
        rcases hn₁ with ⟨i0⟩
        rcases hn₂ with ⟨j0⟩
        exact le_trans (abs_nonneg (X i0 j0))
          (le_trans
            (le_ciSup (Finite.bddAbove_range (fun j : Fin n2 => |X i0 j|)) j0)
            (le_ciSup
              (Finite.bddAbove_range (fun i : Fin n1 => ⨆ j : Fin n2, |X i j|)) i0))
      unfold sampledColumnEnergyMax
      apply ciSup_le
      intro j
      unfold sampledColumnCountMax
      have hcol :
          (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0) ≤
            entrySupNorm X ^ 2 *
              (∑ i : Fin n1, if (i, j) ∈ Omega then (1 : ℝ) else 0) := by
        calc
          (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)
              ≤ ∑ i : Fin n1, if (i, j) ∈ Omega then entrySupNorm X ^ 2 else 0 := by
                apply Finset.sum_le_sum
                intro i _hi
                by_cases hmem : (i, j) ∈ Omega
                · simp [hmem]
                  have hij_abs : |X i j| ≤ entrySupNorm X := by
                    exact le_trans
                      (le_ciSup (Finite.bddAbove_range (fun j : Fin n2 => |X i j|)) j)
                      (le_ciSup
                        (Finite.bddAbove_range
                          (fun i : Fin n1 => ⨆ j : Fin n2, |X i j|)) i)
                  rw [← sq_abs (X i j)]
                  exact sq_le_sq'
                    (le_trans (neg_nonpos.mpr hentry_nonneg) (abs_nonneg (X i j))) hij_abs
                · simp [hmem]
          _ = entrySupNorm X ^ 2 *
              (∑ i : Fin n1, if (i, j) ∈ Omega then (1 : ℝ) else 0) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i _hi
                by_cases hmem : (i, j) ∈ Omega
                · simp [hmem]
                · simp [hmem]
      exact le_trans hcol
        (mul_le_mul_of_nonneg_left
          (le_ciSup
            (Finite.bddAbove_range
              (fun j : Fin n2 =>
                ∑ i : Fin n1, if (i, j) ∈ Omega then (1 : ℝ) else 0)) j)
          (sq_nonneg (entrySupNorm X)))

/-! ### Per-row / per-column moment via marginalization + relaxed Lemma 6.2 -/

/-- `Marginal.rowBern` is `CR2008Lemma62.rowBernoulliMoment`. -/
lemma rowBern_eq {n : ℕ} (q : ℕ) (p : ℝ) :
    Marginal.rowBern n q p = CR2008Lemma62.rowBernoulliMoment n q p := rfl

/-- Per-row q-moment of the row count, bounded by the relaxed Lemma 6.2 scale. -/
lemma per_row_bound {n1 n2 : ℕ} (p : ℝ) (a : Fin n1) (q : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq2np : (q : ℝ) ≤ 2 * ((n2 : ℝ) * p))
    (h1 : 1 ≤ 2 * ((n2 : ℝ) * p)) :
    CR2008Lemma62Max.bExp p
        (fun Omega : Finset (Fin n1 × Fin n2) => (CR2008Lemma62Max.rowCount Omega a : ℝ) ^ q)
      ≤ (4 * ((n2 : ℝ) * p)) ^ q := by
  -- bExp = bExp2, rowCount = rowCount, marginalize to rowBern, then relaxed Lemma 6.2
  have hmarg :
      CR2008Lemma62Max.bExp p
        (fun Omega : Finset (Fin n1 × Fin n2) => (CR2008Lemma62Max.rowCount Omega a : ℝ) ^ q)
        = Marginal.rowBern n2 q p := by
    have := Marginal.bExp2_rowCount_pow_eq_rowBern (n1 := n1) (n2 := n2) p a q
    -- bExp2 ≡ bExp, Marginal.rowCount ≡ CR2008Lemma62Max.rowCount  (definitionally)
    exact this
  rw [hmarg, rowBern_eq]
  exact CR2008Lemma62.rowBernoulliMoment_le_four_np_pow n2 q p hp0 hp1 hq2np h1

/-- Column count of `Ω` in column `b`. -/
noncomputable def colCount {n1 n2 : ℕ} (Omega : Finset (Fin n1 × Fin n2)) (b : Fin n2) : ℕ :=
  (Finset.univ.filter (fun a : Fin n1 => (a, b) ∈ Omega)).card

/-- Image of an observation set under product swap. -/
noncomputable def swapSet {n1 n2 : ℕ} (Omega : Finset (Fin n1 × Fin n2)) :
    Finset (Fin n2 × Fin n1) :=
  Omega.map (Equiv.prodComm (Fin n1) (Fin n2)).toEmbedding

@[simp] lemma mem_swapSet {n1 n2 : ℕ} (Omega : Finset (Fin n1 × Fin n2))
    (c : Fin n2 × Fin n1) : c ∈ swapSet Omega ↔ (c.2, c.1) ∈ Omega := by
  unfold swapSet
  rw [Finset.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩; simpa using ha
  · intro h; exact ⟨(c.2, c.1), h, by simp [Equiv.prodComm]⟩

lemma swapSet_card {n1 n2 : ℕ} (Omega : Finset (Fin n1 × Fin n2)) :
    (swapSet Omega).card = Omega.card := by
  unfold swapSet; rw [Finset.card_map]

/-- Column count equals the row count of the swapped set. -/
lemma colCount_eq_rowCount_swap {n1 n2 : ℕ}
    (Omega : Finset (Fin n1 × Fin n2)) (b : Fin n2) :
    colCount Omega b = CR2008Lemma62Max.rowCount (swapSet Omega) b := by
  unfold colCount CR2008Lemma62Max.rowCount
  congr 1
  apply Finset.filter_congr
  intro a _
  simp [mem_swapSet]

/-- `swapSet` is a bijection on all subsets, so `bExp` of a `colCount` statistic over
`Fin n1 × Fin n2` equals `bExp` of the matching `rowCount` statistic over `Fin n2 × Fin n1`. -/
lemma bExp_colCount_eq_bExp_rowCount {n1 n2 : ℕ} (p : ℝ) (b : Fin n2) (q : ℕ) :
    CR2008Lemma62Max.bExp p
        (fun Omega : Finset (Fin n1 × Fin n2) => (colCount Omega b : ℝ) ^ q)
      = CR2008Lemma62Max.bExp p
        (fun Omega : Finset (Fin n2 × Fin n1) => (CR2008Lemma62Max.rowCount Omega b : ℝ) ^ q) := by
  classical
  unfold CR2008Lemma62Max.bExp
  refine Finset.sum_nbij'
    (i := fun Omega : Finset (Fin n1 × Fin n2) => swapSet Omega)
    (j := fun Omega : Finset (Fin n2 × Fin n1) =>
      Omega.map (Equiv.prodComm (Fin n2) (Fin n1)).toEmbedding)
    (fun Omega _ => Finset.mem_univ _) (fun Omega _ => Finset.mem_univ _)
    ?_ ?_ ?_
  · intro Omega _
    -- left inverse: map (prodComm n2 n1) (swapSet Omega) = Omega
    unfold swapSet
    ext c
    simp only [Finset.mem_map_equiv, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap]
  · intro Omega _
    -- right inverse
    unfold swapSet
    ext c
    simp only [Finset.mem_map_equiv, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap]
  · intro Omega _
    simp only []
    have hcard : Fintype.card (Fin n1 × Fin n2) = Fintype.card (Fin n2 × Fin n1) := by
      rw [Fintype.card_prod, Fintype.card_prod, Nat.mul_comm]
    rw [hcard, swapSet_card, colCount_eq_rowCount_swap]

/-- Per-column q-moment bound (relaxed Lemma 6.2, swapped dimensions). -/
lemma per_col_bound {n1 n2 : ℕ} (p : ℝ) (b : Fin n2) (q : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq2np : (q : ℝ) ≤ 2 * ((n1 : ℝ) * p))
    (h1 : 1 ≤ 2 * ((n1 : ℝ) * p)) :
    CR2008Lemma62Max.bExp p
        (fun Omega : Finset (Fin n1 × Fin n2) => (colCount Omega b : ℝ) ^ q)
      ≤ (4 * ((n1 : ℝ) * p)) ^ q := by
  rw [bExp_colCount_eq_bExp_rowCount]
  exact per_row_bound (n1 := n2) (n2 := n1) p b q hp0 hp1 hq2np h1

/-! ### Exponent window (the genuine content beyond the bricks) -/

/-- The exponent-window lemma under the ONE-sample lower bound `m ≥ β N log N`,
exploiting the relaxed `q ≤ 2·n·p` validity range.  We take `q = ⌈β log N⌉` (at
least `1`) and certify `q ≤ 2·(n_i·p)` for both `i`, i.e. `q ≤ 2·m/N`. -/
lemma q_window_two_np
    (β : ℝ) (hβ : 2 < β) (n₁ n₂ m : ℕ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hm1 : 1 ≤ m)
    (hmLower : (m : ℝ) ≥ β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)))
    (hN2 : 2 ≤ max n₁ n₂) :
    ∃ q : ℕ, 1 ≤ q ∧
      (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
      (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) ∧
      (q : ℝ) ≤ 2 * ((m : ℝ) / ((↑(max n₁ n₂) : ℝ))) := by
  set N := max n₁ n₂ with hN
  have hNpos : 0 < N := lt_of_lt_of_le hn₁ (le_max_left n₁ n₂)
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  set L := Real.log (N : ℝ) with hL
  set q : ℕ := max 1 ⌈β * L⌉₊ with hq
  -- first: m/N ≥ β L  (divide the lower bound by N)
  have hmN : (m : ℝ) / (N : ℝ) ≥ β * L := by
    rw [ge_iff_le, le_div_iff₀ hNR]
    calc β * L * (N : ℝ) = β * (N : ℝ) * L := by ring
      _ ≤ (m : ℝ) := hmLower
  -- N ≥ 2 : β L ≥ β log 2 > 2 log 2 > 1
  have hN2R : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hLpos : Real.log 2 ≤ L := by
    rw [hL]; exact Real.log_le_log (by norm_num) hN2R
  have hlog2 : (0.6931471 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hbetaL : 1 ≤ β * L := by
    have hLge : (0.6931471 : ℝ) ≤ L := le_trans hlog2 hLpos
    have hLnn : 0 ≤ L := le_trans (by norm_num) hLge
    nlinarith [hLge, hβ.le, hLnn]
  -- q = max 1 ⌈β L⌉ = ⌈β L⌉ since β L ≥ 1
  have hceil_ge1 : 1 ≤ ⌈β * L⌉₊ := by
    rw [Nat.one_le_ceil_iff]; linarith
  have hq_eq : q = ⌈β * L⌉₊ := by rw [hq]; omega
  have hqR : (q : ℝ) ≤ β * L + 1 := by
    rw [hq_eq]
    have := Nat.ceil_lt_add_one (a := β * L) (by linarith : (0:ℝ) ≤ β * L)
    linarith
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · exact le_max_left _ _
  · -- q ≥ β L
    have hceil : (⌈β * L⌉₊ : ℝ) ≥ β * L := Nat.le_ceil _
    have : (q : ℝ) ≥ (⌈β * L⌉₊ : ℝ) := by
      have := le_max_right 1 ⌈β * L⌉₊
      exact_mod_cast this
    exact le_trans hceil this
  · -- q ≤ 2 β L
    have : β * L + 1 ≤ 2 * (β * L) := by linarith [hbetaL]
    linarith [hqR, this]
  · -- q ≤ 2 m / N
    have hstep : β * L + 1 ≤ 2 * ((m : ℝ) / (N : ℝ)) := by
      have h2bL : β * L + 1 ≤ 2 * (β * L) := by linarith [hbetaL]
      have : 2 * (β * L) ≤ 2 * ((m : ℝ) / (N : ℝ)) := by linarith [hmN]
      linarith
    linarith [hqR, hstep]

/-! ### Final arithmetic packaging -/

/-- `n ≤ e^q` from `q ≥ β log N`, `n ≤ N`, `β > 1`, `N ≥ 1`. -/
lemma nat_le_exp_q (n N q : ℕ) (β L : ℝ)
    (hβ : 1 ≤ β) (hL : L = Real.log (N : ℝ)) (hNpos : 0 < N)
    (hnN : n ≤ N) (hqL : (q : ℝ) ≥ β * L) :
    (n : ℝ) ≤ Real.exp (q : ℝ) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hnR : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  -- N = exp(log N) = exp L ≤ exp(β L) ≤ exp q
  have hLnn : 0 ≤ L := by rw [hL]; exact Real.log_nonneg (by exact_mod_cast hNpos)
  have h1 : L ≤ β * L := by nlinarith [hLnn, hβ]
  have h2 : (N : ℝ) = Real.exp L := by rw [hL, Real.exp_log hNR]
  calc (n : ℝ) ≤ (N : ℝ) := hnR
    _ = Real.exp L := h2
    _ ≤ Real.exp (β * L) := Real.exp_le_exp.mpr h1
    _ ≤ Real.exp (q : ℝ) := Real.exp_le_exp.mpr hqL

open MatrixCompletion in
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) →
        2 ≤ max n₁ n₂ →
        ∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) ∧
          (q : ℝ) ≤ 2 * (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (↑(max n₁ n₂))) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                (max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X)) ^ q) ≤
            (C * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q := by
  refine ⟨8 * Real.exp 1, by positivity, ?_⟩
  intro β hβ n₁ n₂ m X hn₁ hn₂ hm hmLower hN2
  classical
  set N := max n₁ n₂ with hN
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hn₁R : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0 : ℝ) < (n₂ : ℝ) := by exact_mod_cast hn₂
  have hNpos : 0 < N := lt_of_lt_of_le hn₁ (le_max_left n₁ n₂)
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hn₁N : (n₁ : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_max_left n₁ n₂
  have hn₂N : (n₂ : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_max_right n₁ n₂
  -- Under hN2 (N ≥ 2) and hmLower, m = 0 is impossible: βNlogN > 0.
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · exfalso
    subst hm0
    have hN2' : 2 ≤ N := by rw [hN]; exact hN2
    have hN2R : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2'
    have hlogN_pos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by linarith : (1 : ℝ) < (N : ℝ))
    have hmlow : β * (N : ℝ) * Real.log (N : ℝ) ≤ 0 := by
      rw [hN] at hmLower ⊢; simpa using hmLower
    have hpos : 0 < β * (N : ℝ) * Real.log (N : ℝ) := by
      have hβpos : (0 : ℝ) < β := by linarith
      exact mul_pos (mul_pos hβpos hNR) hlogN_pos
    linarith [hmlow, hpos]
  · -- m ≥ 1 : use the relaxed window
    have hN2' : 2 ≤ max n₁ n₂ := by rw [← hN]; exact hN2
    obtain ⟨q, hq1, hqL, hq2bL, hq2mN⟩ :=
      q_window_two_np β hβ n₁ n₂ m hn₁ hn₂ hmpos hmLower hN2'
    refine ⟨q, hq1, hqL, ?h2bL, ?h2pN, ?_⟩
    case h2bL =>
      -- (q:ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂)))
      simpa [hN] using hq2bL
    case h2pN =>
      -- (q:ℝ) ≤ 2 * (p * N)  with p = m/(n₁n₂)
      have hn₁R' : (0 : ℝ) < (n₁ : ℝ) := hn₁R
      have hn₂R' : (0 : ℝ) < (n₂ : ℝ) := hn₂R
      have hmR0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
      -- n₁n₂ ≤ N²
      have hn1N : (n₁ : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_max_left n₁ n₂
      have hn2N : (n₂ : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_max_right n₁ n₂
      have hprodN : (n₁ : ℝ) * (n₂ : ℝ) ≤ (N : ℝ) * (N : ℝ) :=
        mul_le_mul hn1N hn2N (le_of_lt hn₂R') (le_of_lt (lt_of_lt_of_le hn₁R' hn1N))
      -- m/N ≤ m*N/(n₁n₂)
      have hkey : (m : ℝ) / (N : ℝ) ≤ ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (N : ℝ) := by
        rw [div_mul_eq_mul_div,
          div_le_div_iff₀ hNR (by positivity : (0:ℝ) < (n₁:ℝ)*(n₂:ℝ))]
        have hmono : (m : ℝ) * ((n₁ : ℝ) * (n₂ : ℝ)) ≤ (m : ℝ) * ((N : ℝ) * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hprodN hmR0
        nlinarith [hmono]
      calc (q : ℝ) ≤ 2 * ((m : ℝ) / (N : ℝ)) := by simpa [hN] using hq2mN
        _ ≤ 2 * (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (N : ℝ)) := by linarith [hkey]
        _ = 2 * (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (↑(max n₁ n₂) : ℝ)) := by rw [hN]
    -- 0 ≤ p ≤ 1
    have hp0 : 0 ≤ p := by rw [hp]; positivity
    have hp1 : p ≤ 1 := by
      rw [hp, div_le_one (by positivity)]
      have : (m : ℝ) ≤ (n₁ : ℝ) * (n₂ : ℝ) := by
        have := hm; push_cast; exact_mod_cast this
      linarith
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
    have hsup_nn : 0 ≤ entrySupNorm X := by
      by_cases h₁ : IsEmpty (Fin n₁)
      · exact le_of_eq (by haveI := h₁; simp [entrySupNorm])
      · by_cases h₂ : IsEmpty (Fin n₂)
        · exact le_of_eq (by haveI := h₂; simp [entrySupNorm])
        · have hn1 : Nonempty (Fin n₁) := not_isEmpty_iff.mp h₁
          have hn2 : Nonempty (Fin n₂) := not_isEmpty_iff.mp h₂
          rcases hn1 with ⟨i0⟩; rcases hn2 with ⟨j0⟩
          exact le_trans (abs_nonneg (X i0 j0))
            (le_trans
              (le_ciSup (Finite.bddAbove_range (fun j : Fin n₂ => |X i0 j|)) j0)
              (le_ciSup
                (Finite.bddAbove_range (fun i : Fin n₁ => ⨆ j : Fin n₂, |X i j|)) i0))
    -- `n₂·p = m/n₁ ≥ m/N`, `n₁·p = m/n₂ ≥ m/N`; both ≥ m/N ≥ q/2 and ≥ 1/2.
    have hn2p : (n₂ : ℝ) * p = (m : ℝ) / (n₁ : ℝ) := by
      rw [hp]; field_simp
    have hn1p : (n₁ : ℝ) * p = (m : ℝ) / (n₂ : ℝ) := by
      rw [hp]; field_simp
    have hmN_le_mn1 : (m : ℝ) / (N : ℝ) ≤ (m : ℝ) / (n₁ : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hn₁R hn₁N
    have hmN_le_mn2 : (m : ℝ) / (N : ℝ) ≤ (m : ℝ) / (n₂ : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hn₂R hn₂N
    -- relaxed constraints
    have hq2n2p : (q : ℝ) ≤ 2 * ((n₂ : ℝ) * p) := by
      rw [hn2p]; linarith [hq2mN, hmN_le_mn1]
    have hq2n1p : (q : ℝ) ≤ 2 * ((n₁ : ℝ) * p) := by
      rw [hn1p]; linarith [hq2mN, hmN_le_mn2]
    have hqR1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    have h1_2n2p : 1 ≤ 2 * ((n₂ : ℝ) * p) := by linarith [hqR1, hq2n2p]
    have h1_2n1p : 1 ≤ 2 * ((n₁ : ℝ) * p) := by linarith [hqR1, hq2n1p]
    -- Nonempty instances
    haveI hne1 : Nonempty (Fin n₁) := ⟨⟨0, hn₁⟩⟩
    haveI hne2 : Nonempty (Fin n₂) := ⟨⟨0, hn₂⟩⟩
    -- e^q facts: n₁ ≤ e^q, n₂ ≤ e^q
    have hLdef : Real.log (N : ℝ) = Real.log (N : ℝ) := rfl
    have hn1_exp : (n₁ : ℝ) ≤ Real.exp (q : ℝ) :=
      nat_le_exp_q n₁ N q β (Real.log (N:ℝ)) (le_of_lt (lt_trans one_lt_two hβ)) rfl hNpos
        (le_max_left n₁ n₂) hqL
    have hn2_exp : (n₂ : ℝ) ≤ Real.exp (q : ℝ) :=
      nat_le_exp_q n₂ N q β (Real.log (N:ℝ)) (le_of_lt (lt_trans one_lt_two hβ)) rfl hNpos
        (le_max_right n₁ n₂) hqL
    -- Convert to bExp and split.
    rw [bernoulliExpectation_eq_bExp]
    -- pointwise max^q ≤ rowE^q + colE^q
    have hpt : ∀ Omega : Finset (Fin n₁ × Fin n₂),
        (max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X)) ^ q
          ≤ (sampledRowEnergyMax Omega X) ^ q + (sampledColumnEnergyMax Omega X) ^ q := by
      intro Omega
      have hrnn0 : 0 ≤ sampledRowEnergyMax Omega X := by
        unfold sampledRowEnergyMax
        exact Real.iSup_nonneg (fun i => Finset.sum_nonneg (fun j _ => by positivity))
      have hcnn0 : 0 ≤ sampledColumnEnergyMax Omega X := by
        unfold sampledColumnEnergyMax
        exact Real.iSup_nonneg (fun j => Finset.sum_nonneg (fun i _ => by positivity))
      rcases le_total (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X) with hle | hle
      · rw [max_eq_right hle]
        have hrnn : 0 ≤ (sampledRowEnergyMax Omega X) ^ q := pow_nonneg hrnn0 q
        linarith [hrnn]
      · rw [max_eq_left hle]
        have hcnn : 0 ≤ (sampledColumnEnergyMax Omega X) ^ q := pow_nonneg hcnn0 q
        linarith [hcnn]
    have hsplit :
        CR2008Lemma62Max.bExp p
            (fun Omega => (max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X)) ^ q)
          ≤ CR2008Lemma62Max.bExp p (fun Omega => (sampledRowEnergyMax Omega X) ^ q)
            + CR2008Lemma62Max.bExp p (fun Omega => (sampledColumnEnergyMax Omega X) ^ q) := by
      rw [← CR2008Lemma62Max.bExp_add]
      exact CR2008Lemma62Max.bExp_mono hp0 hp1 hpt
    -- ROW part bound
    have hrow_part :
        CR2008Lemma62Max.bExp p (fun Omega => (sampledRowEnergyMax Omega X) ^ q)
          ≤ (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q := by
      -- rowE^q ≤ (sup²)^q (rowCountMax)^q
      have hstep1 :
          CR2008Lemma62Max.bExp p (fun Omega => (sampledRowEnergyMax Omega X) ^ q)
            ≤ CR2008Lemma62Max.bExp p
                (fun Omega : Finset (Fin n₁ × Fin n₂) =>
                  (entrySupNorm X ^ 2) ^ q * (sampledRowCountMax Omega) ^ q) := by
        apply CR2008Lemma62Max.bExp_mono hp0 hp1
        intro Omega
        have hb := sampledRowEnergyMax_le Omega X
        have hrnn : 0 ≤ sampledRowEnergyMax Omega X := by
          unfold sampledRowEnergyMax
          exact Real.iSup_nonneg (fun i => Finset.sum_nonneg (fun j _ => by positivity))
        calc (sampledRowEnergyMax Omega X) ^ q
            ≤ (entrySupNorm X ^ 2 * sampledRowCountMax Omega) ^ q :=
              pow_le_pow_left₀ hrnn hb q
          _ = (entrySupNorm X ^ 2) ^ q * (sampledRowCountMax Omega) ^ q := mul_pow _ _ q
      rw [CR2008Lemma62Max.bExp_smul] at hstep1
      -- bExp[(rowCountMax)^q] = bExp[(⨆ i rowCount)^q] ≤ n₁ (4 n₂ p)^q
      have hcm : ∀ Omega : Finset (Fin n₁ × Fin n₂),
          (sampledRowCountMax Omega) ^ q
            = (⨆ i : Fin n₁, (CR2008Lemma62Max.rowCount Omega i : ℝ)) ^ q := by
        intro Omega; rw [sampledRowCountMax_eq_iSup]
      have hmax :
          CR2008Lemma62Max.bExp p
              (fun Omega : Finset (Fin n₁ × Fin n₂) => (sampledRowCountMax Omega) ^ q)
            ≤ (n₁ : ℝ) * (4 * ((n₂ : ℝ) * p)) ^ q := by
        rw [show (fun Omega : Finset (Fin n₁ × Fin n₂) => (sampledRowCountMax Omega) ^ q)
              = (fun Omega => (⨆ i : Fin n₁, (CR2008Lemma62Max.rowCount Omega i : ℝ)) ^ q)
            from funext hcm]
        exact CR2008Lemma62Max.bExp_max_rowCount_pow_le hp0 hp1 q
          ((4 * ((n₂ : ℝ) * p)) ^ q)
          (fun a => per_row_bound p a q hp0 hp1 hq2n2p h1_2n2p)
      -- assemble: (sup²)^q * bExp ≤ (sup²)^q * (n₁ (4 n₂ p)^q) ≤ (4e N p sup²)^q
      have hsupq_nn : 0 ≤ (entrySupNorm X ^ 2) ^ q := by positivity
      calc CR2008Lemma62Max.bExp p (fun Omega => (sampledRowEnergyMax Omega X) ^ q)
          ≤ (entrySupNorm X ^ 2) ^ q *
              CR2008Lemma62Max.bExp p (fun Omega => (sampledRowCountMax Omega) ^ q) := hstep1
        _ ≤ (entrySupNorm X ^ 2) ^ q * ((n₁ : ℝ) * (4 * ((n₂ : ℝ) * p)) ^ q) :=
              mul_le_mul_of_nonneg_left hmax hsupq_nn
        _ ≤ (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q := by
              -- n₁ ≤ e^q, n₂ ≤ N, repackage
              have hn2p_nn : 0 ≤ (n₂ : ℝ) * p := by positivity
              have h4 : 0 ≤ 4 * ((n₂ : ℝ) * p) := by positivity
              -- (sup²)^q n₁ (4 n₂ p)^q = n₁ * (4 n₂ p sup²)^q ≤ e^q (4 N p sup²)^q
              have hrw :
                  (entrySupNorm X ^ 2) ^ q * ((n₁ : ℝ) * (4 * ((n₂ : ℝ) * p)) ^ q)
                    = (n₁ : ℝ) * (4 * ((n₂ : ℝ) * p) * entrySupNorm X ^ 2) ^ q := by
                rw [mul_pow]; ring
              rw [hrw]
              have hbase_nn : 0 ≤ 4 * ((n₂ : ℝ) * p) * entrySupNorm X ^ 2 := by positivity
              -- n₁ ≤ e^q
              have hstepA : (n₁ : ℝ) * (4 * ((n₂ : ℝ) * p) * entrySupNorm X ^ 2) ^ q
                  ≤ Real.exp (q : ℝ) * (4 * ((n₂ : ℝ) * p) * entrySupNorm X ^ 2) ^ q :=
                mul_le_mul_of_nonneg_right hn1_exp (by positivity)
              -- e^q = (e)^q ; (4 n₂ p sup²) ≤ (4 N p sup²)
              have hexpq : Real.exp (q : ℝ) = (Real.exp 1) ^ q := by
                rw [← Real.exp_nat_mul]; ring_nf
              have hbase_le : 4 * ((n₂ : ℝ) * p) * entrySupNorm X ^ 2
                  ≤ 4 * ((N : ℝ) * p) * entrySupNorm X ^ 2 := by
                have hstep : (n₂ : ℝ) * p ≤ (N : ℝ) * p :=
                  mul_le_mul_of_nonneg_right hn₂N hp0
                have h4 : 4 * ((n₂ : ℝ) * p) ≤ 4 * ((N : ℝ) * p) :=
                  mul_le_mul_of_nonneg_left hstep (by norm_num)
                exact mul_le_mul_of_nonneg_right h4 (sq_nonneg (entrySupNorm X))
              calc (n₁ : ℝ) * (4 * ((n₂ : ℝ) * p) * entrySupNorm X ^ 2) ^ q
                  ≤ Real.exp (q:ℝ) * (4 * ((n₂ : ℝ) * p) * entrySupNorm X ^ 2) ^ q := hstepA
                _ = (Real.exp 1) ^ q * (4 * ((n₂ : ℝ) * p) * entrySupNorm X ^ 2) ^ q := by
                      rw [hexpq]
                _ ≤ (Real.exp 1) ^ q * (4 * ((N : ℝ) * p) * entrySupNorm X ^ 2) ^ q :=
                      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase_nn hbase_le q)
                        (by positivity)
                _ = (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q := by
                      rw [← mul_pow]; ring_nf
    -- COLUMN part bound (symmetric)
    have hcol_part :
        CR2008Lemma62Max.bExp p (fun Omega => (sampledColumnEnergyMax Omega X) ^ q)
          ≤ (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q := by
      have hstep1 :
          CR2008Lemma62Max.bExp p (fun Omega => (sampledColumnEnergyMax Omega X) ^ q)
            ≤ CR2008Lemma62Max.bExp p
                (fun Omega : Finset (Fin n₁ × Fin n₂) =>
                  (entrySupNorm X ^ 2) ^ q * (sampledColumnCountMax Omega) ^ q) := by
        apply CR2008Lemma62Max.bExp_mono hp0 hp1
        intro Omega
        have hb := sampledColumnEnergyMax_le Omega X
        have hcnn : 0 ≤ sampledColumnEnergyMax Omega X := by
          unfold sampledColumnEnergyMax
          exact Real.iSup_nonneg (fun j => Finset.sum_nonneg (fun i _ => by positivity))
        calc (sampledColumnEnergyMax Omega X) ^ q
            ≤ (entrySupNorm X ^ 2 * sampledColumnCountMax Omega) ^ q :=
              pow_le_pow_left₀ hcnn hb q
          _ = (entrySupNorm X ^ 2) ^ q * (sampledColumnCountMax Omega) ^ q := mul_pow _ _ q
      rw [CR2008Lemma62Max.bExp_smul] at hstep1
      -- sampledColumnCountMax Omega = ⨆ j, colCount Omega j
      have hccm : ∀ Omega : Finset (Fin n₁ × Fin n₂),
          (sampledColumnCountMax Omega) ^ q
            = (⨆ j : Fin n₂, (colCount Omega j : ℝ)) ^ q := by
        intro Omega
        unfold sampledColumnCountMax
        congr 1
        congr 1
        ext j
        unfold colCount
        rw [Finset.sum_boole]
      have hmax :
          CR2008Lemma62Max.bExp p
              (fun Omega : Finset (Fin n₁ × Fin n₂) => (sampledColumnCountMax Omega) ^ q)
            ≤ (n₂ : ℝ) * (4 * ((n₁ : ℝ) * p)) ^ q := by
        rw [show (fun Omega : Finset (Fin n₁ × Fin n₂) => (sampledColumnCountMax Omega) ^ q)
              = (fun Omega => (⨆ j : Fin n₂, (colCount Omega j : ℝ)) ^ q)
            from funext hccm]
        -- max over columns: same engine, with colCount.  Use bExp_max via a colCount version.
        -- reuse bExp_max_rowCount_pow_le on the swapped product? simpler: build directly.
        have hpt2 : ∀ Omega : Finset (Fin n₁ × Fin n₂),
            (⨆ j : Fin n₂, (colCount Omega j : ℝ)) ^ q
              ≤ ∑ j : Fin n₂, ((colCount Omega j : ℝ)) ^ q :=
          fun Omega => CR2008Lemma62Max.max_pow_le_sum_pow
            (fun j => (colCount Omega j : ℝ)) (fun j => by positivity) q
        calc CR2008Lemma62Max.bExp p (fun Omega => (⨆ j : Fin n₂, (colCount Omega j : ℝ)) ^ q)
            ≤ CR2008Lemma62Max.bExp p
                (fun Omega => ∑ j : Fin n₂, ((colCount Omega j : ℝ)) ^ q) :=
              CR2008Lemma62Max.bExp_mono hp0 hp1 hpt2
          _ = ∑ j : Fin n₂, CR2008Lemma62Max.bExp p
                (fun Omega => ((colCount Omega j : ℝ)) ^ q) :=
              CR2008Lemma62Max.bExp_sum p Finset.univ
                (fun j Omega => ((colCount Omega j : ℝ)) ^ q)
          _ ≤ ∑ _j : Fin n₂, (4 * ((n₁ : ℝ) * p)) ^ q :=
              Finset.sum_le_sum (fun j _ => per_col_bound p j q hp0 hp1 hq2n1p h1_2n1p)
          _ = (n₂ : ℝ) * (4 * ((n₁ : ℝ) * p)) ^ q := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hsupq_nn : 0 ≤ (entrySupNorm X ^ 2) ^ q := by positivity
      calc CR2008Lemma62Max.bExp p (fun Omega => (sampledColumnEnergyMax Omega X) ^ q)
          ≤ (entrySupNorm X ^ 2) ^ q *
              CR2008Lemma62Max.bExp p (fun Omega => (sampledColumnCountMax Omega) ^ q) := hstep1
        _ ≤ (entrySupNorm X ^ 2) ^ q * ((n₂ : ℝ) * (4 * ((n₁ : ℝ) * p)) ^ q) :=
              mul_le_mul_of_nonneg_left hmax hsupq_nn
        _ ≤ (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q := by
              have hrw :
                  (entrySupNorm X ^ 2) ^ q * ((n₂ : ℝ) * (4 * ((n₁ : ℝ) * p)) ^ q)
                    = (n₂ : ℝ) * (4 * ((n₁ : ℝ) * p) * entrySupNorm X ^ 2) ^ q := by
                rw [mul_pow]; ring
              rw [hrw]
              have hbase_nn : 0 ≤ 4 * ((n₁ : ℝ) * p) * entrySupNorm X ^ 2 := by positivity
              have hstepA : (n₂ : ℝ) * (4 * ((n₁ : ℝ) * p) * entrySupNorm X ^ 2) ^ q
                  ≤ Real.exp (q : ℝ) * (4 * ((n₁ : ℝ) * p) * entrySupNorm X ^ 2) ^ q :=
                mul_le_mul_of_nonneg_right hn2_exp (by positivity)
              have hexpq : Real.exp (q : ℝ) = (Real.exp 1) ^ q := by
                rw [← Real.exp_nat_mul]; ring_nf
              have hbase_le : 4 * ((n₁ : ℝ) * p) * entrySupNorm X ^ 2
                  ≤ 4 * ((N : ℝ) * p) * entrySupNorm X ^ 2 := by
                have hstep : (n₁ : ℝ) * p ≤ (N : ℝ) * p :=
                  mul_le_mul_of_nonneg_right hn₁N hp0
                have h4 : 4 * ((n₁ : ℝ) * p) ≤ 4 * ((N : ℝ) * p) :=
                  mul_le_mul_of_nonneg_left hstep (by norm_num)
                exact mul_le_mul_of_nonneg_right h4 (sq_nonneg (entrySupNorm X))
              calc (n₂ : ℝ) * (4 * ((n₁ : ℝ) * p) * entrySupNorm X ^ 2) ^ q
                  ≤ Real.exp (q:ℝ) * (4 * ((n₁ : ℝ) * p) * entrySupNorm X ^ 2) ^ q := hstepA
                _ = (Real.exp 1) ^ q * (4 * ((n₁ : ℝ) * p) * entrySupNorm X ^ 2) ^ q := by
                      rw [hexpq]
                _ ≤ (Real.exp 1) ^ q * (4 * ((N : ℝ) * p) * entrySupNorm X ^ 2) ^ q :=
                      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase_nn hbase_le q)
                        (by positivity)
                _ = (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q := by
                      rw [← mul_pow]; ring_nf
    -- Combine row + col ≤ 2 (4e N p sup²)^q ≤ (8e N p sup²)^q = RHS
    have hAnn : 0 ≤ 4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2 := by positivity
    have hfinal :
        (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q
          + (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q
          ≤ (8 * Real.exp 1 * p * (N : ℝ) * entrySupNorm X ^ 2) ^ q := by
      have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ q := by
        calc (2:ℝ) = 2^1 := by norm_num
          _ ≤ 2^q := pow_le_pow_right₀ (by norm_num) hq1
      have hrw : (8 * Real.exp 1 * p * (N : ℝ) * entrySupNorm X ^ 2) ^ q
          = (2:ℝ)^q * (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q := by
        rw [← mul_pow]; ring_nf
      rw [hrw, ← two_mul]
      have hpowAnn : 0 ≤ (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q := by positivity
      exact mul_le_mul_of_nonneg_right h2 hpowAnn
    -- finish
    calc CR2008Lemma62Max.bExp p
            (fun Omega => (max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X)) ^ q)
        ≤ CR2008Lemma62Max.bExp p (fun Omega => (sampledRowEnergyMax Omega X) ^ q)
            + CR2008Lemma62Max.bExp p (fun Omega => (sampledColumnEnergyMax Omega X) ^ q) := hsplit
      _ ≤ (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q
            + (4 * Real.exp 1 * (N : ℝ) * p * entrySupNorm X ^ 2) ^ q :=
            add_le_add hrow_part hcol_part
      _ ≤ (8 * Real.exp 1 * p * (N : ℝ) * entrySupNorm X ^ 2) ^ q := hfinal

end Sol2pNctrl

open MatrixCompletion in
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) →
        2 ≤ max n₁ n₂ →
        ∃ q : ℕ, 1 ≤ q ∧
          (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) ∧
          (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))) ∧
          (q : ℝ) ≤ 2 * (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) * (↑(max n₁ n₂))) ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                (max (sampledRowEnergyMax Omega X) (sampledColumnEnergyMax Omega X)) ^ q) ≤
            (C * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂)) * entrySupNorm X ^ 2) ^ q :=
  Sol2pNctrl.solution
