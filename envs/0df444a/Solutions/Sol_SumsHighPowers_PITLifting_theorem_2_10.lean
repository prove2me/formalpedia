-- Prove2me | solution 1 for SumsHighPowers.PITLifting.theorem_2_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T16:49:50.074619+00:00
-- url     : https://prove2.me/submissions/4cde8c7a-ee16-4b47-89be-3c5b44c96168

import Mathlib
import Definitions.Def_SumsHighPowers_PITLifting_numDistinctRoots
import Definitions.Def_SumsHighPowers_PITLifting_PairwiseNonAssociate

section
open Polynomial

namespace SumsHighPowers.PITLifting.DevWr

noncomputable def wr {A : Type*} [CommRing A] {r : ℕ} (f : Fin r → Polynomial A) : Polynomial A :=
  (Matrix.of fun i j : Fin r => Polynomial.derivative^[(j : ℕ)] (f i)).det

variable {F : Type*} [Field F]

theorem coeff_expand_mul {p : ℕ} (hp : 0 < p) (w g : Polynomial F) (hg : g.natDegree < p)
    (k r : ℕ) (hr : r < p) :
    (expand F p w * g).coeff (p * k + r) = w.coeff k * g.coeff r := by
  rw [Polynomial.coeff_mul]
  rw [Finset.sum_eq_single (p * k, r)]
  · rw [Polynomial.coeff_expand hp]
    simp [Nat.mul_div_cancel_left _ hp]
  · rintro ⟨a, b⟩ hab hne
    have hab := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
    show (expand F p w).coeff a * g.coeff b = 0
    by_cases hb : g.coeff b = 0
    · rw [hb, mul_zero]
    · have hb' : b < p := lt_of_le_of_lt (Polynomial.le_natDegree_of_ne_zero hb) hg
      rw [Polynomial.coeff_expand hp]
      by_cases hdiv : p ∣ a
      · obtain ⟨k', rfl⟩ := hdiv
        exfalso
        apply hne
        have h1 : (p * k' + b) / p = (p * k + r) / p := by rw [hab]
        have h2 : (p * k' + b) % p = (p * k + r) % p := by rw [hab]
        rw [Nat.mul_add_div hp, Nat.mul_add_div hp, Nat.div_eq_of_lt hb',
          Nat.div_eq_of_lt hr] at h1
        rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hb', Nat.mod_eq_of_lt hr] at h2
        simp only [add_zero] at h1
        subst h1; subst h2; rfl
      · simp [hdiv]
  · intro h
    exfalso; apply h
    simp [Finset.mem_antidiagonal]


theorem deriv0 {n : ℕ} (g : Fin n → Polynomial F) (d : ℕ) (hdeg : ∀ i, (g i).natDegree ≤ d)
    (hchar : ringChar F = 0 ∨ d < ringChar F) (v : Fin n → Polynomial F)
    (hv : ∀ i, Polynomial.derivative (v i) = 0) (hsum : ∑ i, v i * g i = 0)
    (hne : ∃ i, v i ≠ 0) : ¬ LinearIndependent F g := by
  rw [Fintype.not_linearIndependent_iff]
  obtain ⟨i0, hi0⟩ := hne
  rcases hchar with h0 | hp
  · haveI : CharZero F := (CharP.ringChar_zero_iff_CharZero F).1 h0
    have hC : ∀ i, v i = Polynomial.C ((v i).coeff 0) := fun i =>
      Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_derivative_eq_zero (hv i))
    refine ⟨fun i => (v i).coeff 0, ?_, i0, ?_⟩
    · have : ∑ i, v i * g i = ∑ i, (v i).coeff 0 • g i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Polynomial.smul_eq_C_mul, ← hC i]
      rw [← this]; exact hsum
    · intro h
      apply hi0; rw [hC i0]; simp only at h; rw [h, map_zero]
  · have hp0 : 0 < ringChar F := lt_of_le_of_lt (Nat.zero_le _) hp
    set p := ringChar F with hpdef
    haveI : CharP F p := ringChar.charP F
    have hw : ∀ i, Polynomial.expand F p (Polynomial.contract p (v i)) = v i :=
      fun i => Polynomial.expand_contract p (hv i) hp0.ne'
    set w : Fin n → Polynomial F := fun i => Polynomial.contract p (v i) with hwdef
    have hw0 : w i0 ≠ 0 := by
      intro h; apply hi0; rw [← hw i0]; simp only [hwdef] at h; rw [h]; simp
    obtain ⟨k, hk⟩ : ∃ k, (w i0).coeff k ≠ 0 := by
      by_contra hcon; push Not at hcon; exact hw0 (Polynomial.ext (by simpa using hcon))
    refine ⟨fun i => (w i).coeff k, ?_, i0, hk⟩
    ext r
    rw [Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_smul, smul_eq_mul, Polynomial.coeff_zero]
    by_cases hr : r < p
    · have h1 := congrArg (fun q => q.coeff (p * k + r)) hsum
      simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_zero] at h1
      rw [← h1]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← hw i, coeff_expand_mul hp0 (w i) (g i) (lt_of_le_of_lt (hdeg i) hp) k r hr]
    · refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := g i)
        (lt_of_le_of_lt (hdeg i) (lt_of_lt_of_le hp (not_lt.1 hr))), mul_zero]


theorem normalize_step {m : ℕ} (g : Fin m → Polynomial F) (d : ℕ) (hdeg : ∀ i, (g i).natDegree ≤ d)
    (hchar : ringChar F = 0 ∨ d < ringChar F) (l : Fin m) (v : Fin m → Polynomial F)
    (hl : v l ≠ 0)
    (hode : ∀ i, v l * Polynomial.derivative (v i) = Polynomial.derivative (v l) * v i)
    (hsum : ∑ i, v i * g i = 0) : ¬ LinearIndependent F g := by
  classical
  obtain ⟨v', hv1, hv2⟩ := Finset.extract_gcd v (Finset.univ_nonempty_iff.2 ⟨l⟩)
  set u := Finset.univ.gcd v with hu
  have hu0 : u ≠ 0 := by
    intro h0
    rw [hu, Finset.gcd_eq_zero_iff] at h0
    exact hl (h0 l (Finset.mem_univ _))
  have hsum' : ∑ i, v' i * g i = 0 := by
    have : u * ∑ i, v' i * g i = 0 := by
      rw [Finset.mul_sum, ← hsum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hv1 i (Finset.mem_univ _)]; ring
    exact (mul_eq_zero.1 this).resolve_left hu0
  have hl' : v' l ≠ 0 := by
    intro h0; apply hl; rw [hv1 l (Finset.mem_univ _), h0, mul_zero]
  have hode' : ∀ i, v' l * Polynomial.derivative (v' i) = Polynomial.derivative (v' l) * v' i := by
    intro i
    have h1 := hode i
    rw [hv1 l (Finset.mem_univ _), hv1 i (Finset.mem_univ _)] at h1
    simp only [Polynomial.derivative_mul] at h1
    have h2 : u ^ 2 * (v' l * Polynomial.derivative (v' i)) =
        u ^ 2 * (Polynomial.derivative (v' l) * v' i) := by
      linear_combination h1
    exact mul_left_cancel₀ (pow_ne_zero 2 hu0) h2
  have hdvd : v' l ∣ Polynomial.derivative (v' l) := by
    have h1 : v' l ∣ Finset.univ.gcd (fun i => Polynomial.derivative (v' l) * v' i) :=
      Finset.dvd_gcd (fun i _ => ⟨Polynomial.derivative (v' i), (hode' i).symm⟩)
    rw [Finset.gcd_mul_left, hv2, mul_one] at h1
    exact h1.trans (normalize_associated _).dvd
  have hd0 : Polynomial.derivative (v' l) = 0 := by
    by_contra hne
    have h1 := Polynomial.natDegree_le_of_dvd hdvd hne
    by_cases hdg : (v' l).natDegree = 0
    · apply hne
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdg]; simp
    · have := Polynomial.natDegree_derivative_lt hdg
      omega
  refine deriv0 g d hdeg hchar v' (fun i => ?_) hsum' ⟨l, hl'⟩
  have := hode' i
  rw [hd0, zero_mul] at this
  exact (mul_eq_zero.1 this).resolve_left hl'


theorem step {n : ℕ} (g : Fin (n + 1) → Polynomial F)
    (hW' : wr (fun i : Fin n => g i.castSucc) ≠ 0) (hW : wr g = 0) :
    ∃ v : Fin (n + 1) → Polynomial F, v (Fin.last n) ≠ 0 ∧
      (∀ i, v (Fin.last n) * Polynomial.derivative (v i) =
        Polynomial.derivative (v (Fin.last n)) * v i) ∧ ∑ i, v i * g i = 0 := by
  classical
  unfold wr at hW hW'
  obtain ⟨v, hv0, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hW
  have hrel : ∀ j : ℕ, j ≤ n → ∑ i, v i * Polynomial.derivative^[j] (g i) = 0 := by
    intro j hj
    have := congrFun hvM ⟨j, by omega⟩
    simpa [Matrix.vecMul, dotProduct] using this
  -- first n columns, rows castSucc
  have hcut : ∀ (w : Fin (n + 1) → Polynomial F), w (Fin.last n) = 0 →
      (∀ j : ℕ, j < n → ∑ i, w i * Polynomial.derivative^[j] (g i) = 0) →
      (∀ i : Fin n, w i.castSucc = 0) := by
    intro w hwl hwr
    by_contra hcon
    push Not at hcon
    obtain ⟨i1, hi1⟩ := hcon
    have hex : ∃ w' : Fin n → Polynomial F, w' ≠ 0 ∧
        Matrix.vecMul w' (Matrix.of fun i j : Fin n => Polynomial.derivative^[(j : ℕ)] (g i.castSucc)) = 0 := by
      refine ⟨fun i => w i.castSucc, fun h => hi1 (congrFun h i1), ?_⟩
      funext j
      have := hwr j j.2
      rw [Fin.sum_univ_castSucc, hwl, zero_mul, add_zero] at this
      simpa [Matrix.vecMul, dotProduct] using this
    exact hW' (Matrix.exists_vecMul_eq_zero_iff.1 hex)
  have hlast : v (Fin.last n) ≠ 0 := by
    intro h0
    apply hv0
    have := hcut v h0 (fun j hj => hrel j (by omega))
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using h0
    · simpa using this i
  set w : Fin (n + 1) → Polynomial F := fun i =>
    v (Fin.last n) * Polynomial.derivative (v i) - Polynomial.derivative (v (Fin.last n)) * v i
    with hwdef
  have hwl : w (Fin.last n) = 0 := by simp only [hwdef]; ring
  have hwr : ∀ j : ℕ, j < n → ∑ i, w i * Polynomial.derivative^[j] (g i) = 0 := by
    intro j hj
    have h1 := hrel j (by omega)
    have h2 := hrel (j + 1) (by omega)
    have h3 : ∑ i, Polynomial.derivative (v i) * Polynomial.derivative^[j] (g i) = 0 := by
      have := congrArg Polynomial.derivative h1
      rw [map_sum, map_zero] at this
      simp only [Polynomial.derivative_mul] at this
      rw [Finset.sum_add_distrib] at this
      have h4 : ∑ i, v i * Polynomial.derivative (Polynomial.derivative^[j] (g i)) = 0 := by
        simpa [Function.iterate_succ_apply'] using h2
      rw [h4, add_zero] at this
      exact this
    have : ∑ i, w i * Polynomial.derivative^[j] (g i) =
        v (Fin.last n) * ∑ i, Polynomial.derivative (v i) * Polynomial.derivative^[j] (g i) -
        Polynomial.derivative (v (Fin.last n)) * ∑ i, v i * Polynomial.derivative^[j] (g i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hwdef]; ring
    rw [this, h1, h3]; ring
  have hw0 := hcut w hwl hwr
  refine ⟨v, hlast, fun i => ?_, by simpa using hrel 0 (Nat.zero_le _)⟩
  refine Fin.lastCases ?_ (fun i => ?_) i
  · ring
  · have := hw0 i
    simp only [hwdef] at this
    exact sub_eq_zero.1 this


theorem iter_sum {ι : Type*} (j : ℕ) (s : Finset ι) (f : ι → Polynomial F) :
    Polynomial.derivative^[j] (∑ i ∈ s, f i) = ∑ i ∈ s, Polynomial.derivative^[j] (f i) := by
  induction j with
  | zero => simp
  | succ k ih => simp [Function.iterate_succ_apply', ih, map_sum]

theorem dep_of_wr_zero (d : ℕ) (hchar : ringChar F = 0 ∨ d < ringChar F) :
    ∀ (n : ℕ) (g : Fin n → Polynomial F), (∀ i, (g i).natDegree ≤ d) →
      wr g = 0 → ¬ LinearIndependent F g := by
  intro n
  induction n with
  | zero =>
    intro g _ hW
    exfalso
    unfold wr at hW
    simp at hW
  | succ n ih =>
    intro g hdeg hW
    by_cases hW' : wr (fun i : Fin n => g i.castSucc) = 0
    · intro hLI
      exact ih (fun i => g i.castSucc) (fun i => hdeg _) hW'
        (hLI.comp Fin.castSucc (Fin.castSucc_injective n))
    · obtain ⟨v, hv1, hv2, hv3⟩ := step g hW' hW
      exact normalize_step g d hdeg hchar (Fin.last n) v hv1 hv2 hv3

end SumsHighPowers.PITLifting.DevWr
end

section
open Polynomial

namespace SumsHighPowers.PITLifting.DevAbc

open SumsHighPowers.PITLifting.DevWr

variable {K : Type*} [Field K]

theorem pow_dvd_derivative (α : K) (e : ℕ) (f : K[X]) (h : (X - C α) ^ e ∣ f) :
    (X - C α) ^ (e - 1) ∣ derivative f := by
  obtain ⟨g, rfl⟩ := h
  rcases e with _ | k
  · simp
  · rw [derivative_mul, derivative_pow]
    simp only [Nat.add_sub_cancel, derivative_sub, derivative_X, derivative_C, sub_zero, mul_one]
    refine dvd_add ?_ ?_
    · exact ⟨C ((k + 1 : ℕ) : K) * g, by simp; ring⟩
    · exact ⟨(X - C α) * derivative g, by ring⟩

theorem pow_dvd_iter_derivative (α : K) (j : ℕ) : ∀ (e : ℕ) (f : K[X]),
    (X - C α) ^ e ∣ f → (X - C α) ^ (e - j) ∣ derivative^[j] f := by
  induction j with
  | zero => intro e f h; simpa using h
  | succ j ih =>
    intro e f h
    have := ih (e - 1) (derivative f) (pow_dvd_derivative α e f h)
    rw [Function.iterate_succ_apply]
    have h2 : e - 1 - j = e - (j + 1) := by omega
    rwa [h2] at this

theorem wr_dvd {m : ℕ} (g : Fin m → K[X]) (α : K) (e : Fin m → ℕ)
    (h : ∀ i, (X - C α) ^ (e i) ∣ g i) :
    (X - C α) ^ (∑ i, (e i - (m - 1))) ∣ wr g := by
  unfold wr
  rw [Matrix.det_apply]
  refine Finset.dvd_sum (fun σ _ => ?_)
  rw [Units.smul_def, zsmul_eq_mul]
  refine Dvd.dvd.mul_left ?_ _
  have h1 : ∀ j : Fin m, (X - C α) ^ (e (σ j) - j) ∣
      (Matrix.of fun i j : Fin m => derivative^[(j : ℕ)] (g i)) (σ j) j := fun j =>
    pow_dvd_iter_derivative α j _ _ (h (σ j))
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_dvd _ _ (fun j _ => h1 j))
  rw [Finset.prod_pow_eq_pow_sum]
  refine pow_dvd_pow _ ?_
  rw [← Equiv.sum_comp σ (fun i => e i - (m - 1))]
  exact Finset.sum_le_sum (fun j _ => Nat.sub_le_sub_left (by have := j.2; omega) _)

theorem natDegree_wr_add_le {m : ℕ} (g : Fin m → K[X]) (hW : wr g ≠ 0) :
    (wr g).natDegree + ∑ j : Fin m, (j : ℕ) ≤ ∑ i, (g i).natDegree := by
  classical
  set M : Matrix (Fin m) (Fin m) K[X] := Matrix.of fun i j : Fin m => derivative^[(j : ℕ)] (g i)
    with hM
  have hMe : ∀ i j, M i j = derivative^[(j : ℕ)] (g i) := fun _ _ => rfl
  have hwr : wr g = M.det := rfl
  rw [hwr] at hW ⊢
  rw [Matrix.det_apply] at hW ⊢
  have hterm : ∀ σ : Equiv.Perm (Fin m),
      (Equiv.Perm.sign σ • ∏ j, M (σ j) j) ≠ 0 → (∀ j : Fin m, (j : ℕ) ≤ (g (σ j)).natDegree) := by
    intro σ hσ j
    by_contra hlt
    push Not at hlt
    apply hσ
    have : M (σ j) j = 0 := by
      rw [hMe]
      exact iterate_derivative_eq_zero hlt
    rw [Finset.prod_eq_zero (f := fun x => M (σ x) x) (Finset.mem_univ j) this, smul_zero]
  have hsum : ∑ j : Fin m, (j : ℕ) ≤ ∑ i, (g i).natDegree := by
    obtain ⟨σ, _, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hW
    rw [← Equiv.sum_comp σ (fun i => (g i).natDegree)]
    exact Finset.sum_le_sum (fun j _ => hterm σ hσ j)
  have hdeg : (∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ • ∏ j, M (σ j) j).natDegree
      ≤ ∑ i, (g i).natDegree - ∑ j : Fin m, (j : ℕ) := by
    refine natDegree_sum_le_of_forall_le _ _ (fun σ _ => ?_)
    by_cases hσ : (Equiv.Perm.sign σ • ∏ j, M (σ j) j) = 0
    · rw [hσ]; simp
    · have hj := hterm σ hσ
      have h1 : (Equiv.Perm.sign σ • ∏ j, M (σ j) j).natDegree ≤ (∏ j, M (σ j) j).natDegree := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp [natDegree_neg]
      refine h1.trans ((natDegree_prod_le _ _).trans ?_)
      have h2 : ∀ j : Fin m, (M (σ j) j).natDegree ≤ (g (σ j)).natDegree - j := fun j => by
        rw [hMe]; exact natDegree_iterate_derivative _ _
      refine (Finset.sum_le_sum (fun j _ => h2 j)).trans ?_
      have h3 : ∑ j : Fin m, ((g (σ j)).natDegree - (j : ℕ)) + ∑ j : Fin m, (j : ℕ)
          = ∑ i, (g i).natDegree := by
        rw [← Finset.sum_add_distrib, ← Equiv.sum_comp σ (fun i => (g i).natDegree)]
        exact Finset.sum_congr rfl (fun j _ => Nat.sub_add_cancel (hj j))
      omega
  omega


theorem wr_update_sum {m : ℕ} (g : Fin m → K[X]) (kj : Fin m) (P : K[X]) (hP : P = ∑ k, g k) :
    wr (Function.update g kj P) = wr g := by
  classical
  unfold wr
  set M : Matrix (Fin m) (Fin m) K[X] := Matrix.of fun i j : Fin m => derivative^[(j : ℕ)] (g i)
    with hM
  have h1 : (Matrix.of fun i j : Fin m => derivative^[(j : ℕ)] (Function.update g kj P i))
      = M.updateRow kj (∑ k, (1 : K[X]) • M k) := by
    refine Matrix.ext (fun i j => ?_)
    by_cases hi : i = kj
    · subst hi
      simp only [Matrix.of_apply, Function.update_self, Matrix.updateRow_self, Finset.sum_apply,
        Pi.smul_apply, one_smul, hM, hP]
      rw [DevWr.iter_sum (F := K)]
      exact (Finset.sum_apply j Finset.univ (fun x => (Matrix.of fun i j : Fin m => derivative^[(j : ℕ)] (g i)) x)).symm
    · simp [Matrix.updateRow_ne hi, hM, hi]
  rw [h1, Matrix.det_updateRow_sum]
  simp


theorem sum_rootMult_le (Q : K[X]) (S : Finset K) :
    ∑ α ∈ S, rootMultiplicity α Q ≤ Q.natDegree := by
  classical
  simp_rw [← count_roots]
  refine le_trans ?_ (card_roots' Q)
  rw [← Multiset.toFinset_sum_count_eq]
  rw [← Finset.sum_filter_of_ne (p := fun a => a ∈ Q.roots.toFinset) (fun a _ ha => by
    by_contra h
    exact ha (Multiset.count_eq_zero.2 (by simpa using h)))]
  exact Finset.sum_le_sum_of_subset (fun a ha => (Finset.mem_filter.1 ha).2)

open Classical in
theorem natDegree_eq_sum_rootMult [IsAlgClosed K] (Q : K[X]) :
    ∑ α ∈ Q.roots.toFinset, rootMultiplicity α Q = Q.natDegree := by
  classical
  simp_rw [← count_roots]
  rw [Multiset.toFinset_sum_count_eq]
  exact (IsAlgClosed.splits Q).natDegree_eq_card_roots.symm


theorem wr_map {F : Type*} [Field F] (φ : F →+* K) {m : ℕ} (g : Fin m → F[X]) :
    wr (fun k => (g k).map φ) = (wr g).map φ := by
  unfold wr
  have h : ∀ (j : ℕ) (p : F[X]), derivative^[j] (p.map φ) = (derivative^[j] p).map φ := by
    intro j; induction j with
    | zero => intro p; rfl
    | succ j ih =>
      intro p
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, derivative_map, ih]
  have := RingHom.map_det (Polynomial.mapRingHom φ)
    (Matrix.of fun i j : Fin m => derivative^[(j : ℕ)] (g i))
  show _ = (Polynomial.mapRingHom φ) _
  rw [this]
  congr 1
  refine Matrix.ext (fun i j => ?_)
  simp [h]

theorem exists_nonroot {F : Type*} [Field F] {n : ℕ} (f : Fin n → F[X])
    (hgcd : ∀ q : F[X], (∀ i, q ∣ f i) → IsUnit q) (α : AlgebraicClosure F) :
    ∃ j, rootMultiplicity α ((f j).map (algebraMap F (AlgebraicClosure F))) = 0 := by
  by_contra hcon
  push Not at hcon
  apply minpoly.not_isUnit F α
  apply hgcd
  intro i
  apply minpoly.dvd
  have := hcon i
  have hpos := Nat.pos_of_ne_zero this
  rw [rootMultiplicity_pos'] at hpos
  have h2 := hpos.2
  rw [IsRoot.def, eval_map] at h2
  simpa [Polynomial.aeval_def] using h2


open Classical in
theorem indep_core {F : Type*} [Field F] (m : ℕ) (f : Fin (m + 1) → F[X])
    (hsum : ∑ i, f i = 0)
    (hgcd : ∀ q : F[X], (∀ i, q ∣ f i) → IsUnit q)
    (D : ℕ) (hdeg : ∀ i, (f i).natDegree ≤ D)
    (hchar : ringChar F = 0 ∨ D < ringChar F)
    (hli : LinearIndependent F (fun i : Fin m => f i.castSucc)) :
    (f (Fin.last m)).natDegree + ∑ j : Fin m, (j : ℕ) ≤
      (m - 1) * ∑ i, numDistinctRoots (f i) := by
  set K := AlgebraicClosure F with hK
  set φ : F →+* K := algebraMap F K with hφ
  set fK : Fin (m + 1) → K[X] := fun i => (f i).map φ with hfK
  set g : Fin m → F[X] := fun k => f k.castSucc with hg
  have hW : wr g ≠ 0 := fun h0 => dep_of_wr_zero D hchar m g (fun k => hdeg _) h0 hli
  have hWK : wr (fun k : Fin m => fK k.castSucc) ≠ 0 := by
    have : wr (fun k : Fin m => fK k.castSucc) = (wr g).map φ := wr_map φ g
    rw [this]; exact (Polynomial.map_ne_zero_iff φ.injective).2 hW
  have hWKdeg : (wr (fun k : Fin m => fK k.castSucc)).natDegree = (wr g).natDegree := by
    have : wr (fun k : Fin m => fK k.castSucc) = (wr g).map φ := wr_map φ g
    rw [this, natDegree_map]
  have hsumK : ∑ i, fK i = 0 := by
    have : (∑ i, f i).map φ = ∑ i, (f i).map φ := by
      simp [Polynomial.map_sum]
    rw [← this, hsum]; simp
  set e : Fin (m + 1) → K → ℕ := fun i α => rootMultiplicity α (fK i) with he
  have hdv : ∀ i α, (X - C α) ^ (e i α) ∣ fK i := fun i α => pow_rootMultiplicity_dvd _ _
  have hbound : ∀ α : K, ∑ i, (e i α - (m - 1)) ≤ rootMultiplicity α (wr (fun k : Fin m => fK k.castSucc)) := by
    intro α
    obtain ⟨j, hj⟩ := exists_nonroot f hgcd α
    have hj' : e j α = 0 := hj
    rw [le_rootMultiplicity_iff hWK]
    rw [Fin.sum_univ_castSucc]
    by_cases hjl : j = Fin.last m
    · subst hjl
      have := wr_dvd (fun k : Fin m => fK k.castSucc) α (fun k : Fin m => e k.castSucc α) (fun k => hdv _ _)
      rw [hj']; simpa using this
    · obtain ⟨kj, rfl⟩ := Fin.exists_castSucc_eq.2 hjl
      have hP : -(fK (Fin.last m)) = ∑ k : Fin m, fK k.castSucc := by
        have := hsumK
        rw [Fin.sum_univ_castSucc] at this
        exact eq_neg_of_add_eq_zero_left this |>.symm
      have hupd := wr_update_sum (fun k : Fin m => fK k.castSucc) kj (-(fK (Fin.last m))) hP
      set e' : Fin m → ℕ := Function.update (fun k : Fin m => e k.castSucc α) kj (e (Fin.last m) α) with he'
      have hdiv' : ∀ k, (X - C α) ^ (e' k) ∣
          (Function.update (fun k : Fin m => fK k.castSucc) kj (-(fK (Fin.last m)))) k := by
        intro k
        by_cases hk : k = kj
        · subst hk
          simp only [he', Function.update_self]
          exact (dvd_neg).2 (hdv _ _)
        · simp only [he', Function.update_of_ne hk]
          exact hdv _ _
      have hd := wr_dvd _ α e' hdiv'
      rw [hupd] at hd
      have key : ∑ k : Fin m, (e' k - (m - 1)) + (e kj.castSucc α - (m - 1)) =
          ∑ k : Fin m, (e k.castSucc α - (m - 1)) + (e (Fin.last m) α - (m - 1)) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ kj),
          ← Finset.add_sum_erase Finset.univ (fun k : Fin m => e k.castSucc α - (m - 1)) (Finset.mem_univ kj)]
        have : ∑ k ∈ Finset.univ.erase kj, (e' k - (m - 1)) =
            ∑ k ∈ Finset.univ.erase kj, (e k.castSucc α - (m - 1)) :=
          Finset.sum_congr rfl (fun k hk => by
            simp [he', Function.update_of_ne (Finset.ne_of_mem_erase hk)])
        rw [this]
        simp only [he', Function.update_self]
        omega
      rw [hj'] at key
      have : ∑ k : Fin m, (e' k - (m - 1)) = ∑ k : Fin m, (e k.castSucc α - (m - 1)) + (e (Fin.last m) α - (m - 1)) := by
        simpa using key
      rw [hj'] at *
      rw [← this]
      simpa [hj'] using hd
  set S : Finset K := Finset.univ.biUnion (fun i => (fK i).roots.toFinset) with hS
  have hA : ∑ α ∈ S, ∑ i, (e i α - (m - 1)) ≤ (wr g).natDegree := by
    calc ∑ α ∈ S, ∑ i, (e i α - (m - 1))
        ≤ ∑ α ∈ S, rootMultiplicity α (wr (fun k : Fin m => fK k.castSucc)) :=
          Finset.sum_le_sum (fun α _ => hbound α)
      _ ≤ (wr (fun k : Fin m => fK k.castSucc)).natDegree := sum_rootMult_le _ _
      _ = (wr g).natDegree := hWKdeg
  have hB : ∀ i, (f i).natDegree ≤ ∑ α ∈ S, (e i α - (m - 1)) +
      (m - 1) * numDistinctRoots (f i) := by
    intro i
    have hSi : (fK i).roots.toFinset ⊆ S := Finset.subset_biUnion_of_mem
      (fun i => (fK i).roots.toFinset) (Finset.mem_univ i)
    have hd : (f i).natDegree = ∑ α ∈ (fK i).roots.toFinset, e i α := by
      rw [← natDegree_map (p := f i) φ]
      exact (natDegree_eq_sum_rootMult (fK i)).symm
    have hν : numDistinctRoots (f i) = (fK i).roots.toFinset.card := rfl
    calc (f i).natDegree = ∑ α ∈ (fK i).roots.toFinset, e i α := hd
      _ ≤ ∑ α ∈ (fK i).roots.toFinset, ((e i α - (m - 1)) + (m - 1)) :=
          Finset.sum_le_sum (fun α _ => by omega)
      _ = ∑ α ∈ (fK i).roots.toFinset, (e i α - (m - 1)) + (m - 1) * numDistinctRoots (f i) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, hν, mul_comm]
      _ ≤ _ := by
          gcongr
  have hC : ∑ i, (f i).natDegree ≤ (wr g).natDegree + (m - 1) * ∑ i, numDistinctRoots (f i) := by
    calc ∑ i, (f i).natDegree
        ≤ ∑ i, (∑ α ∈ S, (e i α - (m - 1)) + (m - 1) * numDistinctRoots (f i)) :=
          Finset.sum_le_sum (fun i _ => hB i)
      _ = ∑ α ∈ S, ∑ i, (e i α - (m - 1)) + (m - 1) * ∑ i, numDistinctRoots (f i) := by
          rw [Finset.sum_add_distrib, Finset.sum_comm, Finset.mul_sum]
      _ ≤ _ := by gcongr
  have hE := natDegree_wr_add_le g hW
  have hg' : ∑ i, (g i).natDegree = ∑ i : Fin m, (f i.castSucc).natDegree := rfl
  rw [Fin.sum_univ_castSucc] at hC
  rw [hg'] at hE
  omega

end SumsHighPowers.PITLifting.DevAbc
end

section
namespace SumsHighPowers.PITLifting.Dev210

open SumsHighPowers.PITLifting

theorem nu_le {F : Type*} [Field F] (c : F) (hc : c ≠ 0) (g : Polynomial F) (d : ℕ) (hd : d ≠ 0) :
    numDistinctRoots (c • g ^ d) ≤ g.natDegree := by
  unfold numDistinctRoots
  classical
  rw [Polynomial.smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
    Polynomial.roots_C_mul _ (by simpa using hc), Polynomial.roots_pow]
  rw [Multiset.toFinset_nsmul _ _ hd]
  refine (Multiset.toFinset_card_le _).trans ?_
  refine (Polynomial.card_roots' _).trans ?_
  rw [Polynomial.natDegree_map]

theorem natDegree_smul_pow {F : Type*} [Field F] (c : F) (hc : c ≠ 0) (g : Polynomial F) (d : ℕ) :
    (c • g ^ d).natDegree = d * g.natDegree := by
  rw [Polynomial.smul_eq_C_mul, Polynomial.natDegree_C_mul hc, Polynomial.natDegree_pow]


open Classical in
theorem core {F : Type*} [Field F] (r d δ : ℕ) (hr : 3 ≤ r)
    (hchar : ringChar F = 0 ∨ (r - 1) * d * δ < ringChar F)
    (f : Fin r → Polynomial F) (hna : PairwiseNonAssociate (F := F) f)
    (hdeg : ∀ i, (f i).natDegree ≤ δ)
    (hrd : (r - 1) ^ 2 ≤ d + 1)
    (c : Fin r → F)
    (hsum : ∑ i, c i • f i ^ d = 0)
    (hmin : ∀ c' : Fin r → F, ∑ i, c' i • f i ^ d = 0 → (∃ i, c' i ≠ 0) →
      (Finset.univ.filter (fun i => c i ≠ 0)).card ≤ (Finset.univ.filter (fun i => c' i ≠ 0)).card)
    (hne : ∃ i, c i ≠ 0) : False := by
  set T := Finset.univ.filter (fun i => c i ≠ 0) with hTdef
  have hmemT : ∀ i, i ∈ T ↔ c i ≠ 0 := by intro i; simp [hTdef]
  have hd3 : 3 ≤ d := by
    have : 4 ≤ (r - 1) ^ 2 := by nlinarith [Nat.sub_add_cancel (show 1 ≤ r by omega)]
    omega
  have hd0 : d ≠ 0 := by omega
  have hfne : ∀ i, f i ≠ 0 := by
    intro i h0
    obtain ⟨j, hj⟩ : ∃ j : Fin r, j ≠ i := by
      by_cases h0 : i = ⟨0, by omega⟩
      · exact ⟨⟨1, by omega⟩, by rw [h0]; simp [Fin.ext_iff]⟩
      · exact ⟨⟨0, by omega⟩, fun h => h0 h.symm⟩
    have := LinearIndependent.pair_iff.1 (hna i j hj.symm) 1 0 (by simp [h0])
    simp at this
  have hTne : T.Nonempty := by
    obtain ⟨i, hi⟩ := hne; exact ⟨i, (hmemT i).2 hi⟩
  obtain ⟨g, hg1, hg2⟩ := Finset.extract_gcd f hTne
  set P := T.gcd f with hPdef
  have hP0 : P ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := hTne
    have := hg1 i hi
    rw [h0, zero_mul] at this
    exact hfne i this
  have hgne : ∀ i ∈ T, g i ≠ 0 := by
    intro i hi h0
    have := hg1 i hi
    rw [h0, mul_zero] at this
    exact hfne i this
  have hcsumT : ∑ i ∈ T, c i • f i ^ d = 0 := by
    rw [← hsum, hTdef]
    refine Finset.sum_filter_of_ne (fun x _ hx => ?_)
    intro h0; apply hx; simp [h0]
  have hgsum : ∑ i ∈ T, c i • g i ^ d = 0 := by
    have h1 : ∑ i ∈ T, c i • f i ^ d = P ^ d * ∑ i ∈ T, c i • g i ^ d := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [hg1 i hi, mul_pow, Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]; ring
    rw [h1] at hcsumT
    exact (mul_eq_zero.1 hcsumT).resolve_left (pow_ne_zero _ hP0)
  obtain ⟨k, hkT, hkmax⟩ := Finset.exists_max_image T (fun i => (g i).natDegree) hTne
  set e' := (g k).natDegree with he'
  have hm2 : 2 ≤ T.card := by
    by_contra hlt
    have h1 : T.card = 1 := by have := Finset.card_pos.2 hTne; omega
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 h1
    rw [hi, Finset.sum_singleton] at hgsum
    have hiT : i ∈ T := by rw [hi]; simp
    exact smul_ne_zero ((hmemT i).1 hiT) (pow_ne_zero _ (hgne i hiT)) hgsum
  set m := T.card with hm
  have hmr : m ≤ r := by
    have := Finset.card_le_univ T; simpa using this
  have hEcard : (T.erase k).card = m - 1 := Finset.card_erase_of_mem hkT
  let eq : (T.erase k) ≃ Fin (m - 1) := Finset.equivFinOfCardEq hEcard
  have heT : ∀ i : Fin (m - 1), ((eq.symm i : T.erase k) : Fin r) ∈ T :=
    fun i => Finset.mem_of_mem_erase (eq.symm i).2
  have hek : ∀ i : Fin (m - 1), ((eq.symm i : T.erase k) : Fin r) ≠ k :=
    fun i => Finset.ne_of_mem_erase (eq.symm i).2
  have hcne : ∀ i : Fin (m - 1), c (eq.symm i : T.erase k) ≠ 0 := fun i => (hmemT _).1 (heT i)
  let h : Fin (m - 1) → Polynomial F := fun i => c (eq.symm i : T.erase k) • g (eq.symm i : T.erase k) ^ d
  have hsumh : ∑ i, h i = (-c k) • g k ^ d := by
    have h1 : ∑ i, h i = ∑ x ∈ T.erase k, c x • g x ^ d := by
      show ∑ i, (fun x : T.erase k => c x • g x ^ d) (eq.symm i) = _
      rw [Equiv.sum_comp eq.symm (fun x : T.erase k => c x • g x ^ d)]
      exact Finset.sum_coe_sort (T.erase k) (fun x => c x • g x ^ d)
    rw [h1, neg_smul]
    have := Finset.add_sum_erase T (fun x => c x • g x ^ d) hkT
    rw [hgsum] at this
    exact eq_neg_of_add_eq_zero_right this
  have hck : c k ≠ 0 := (hmemT k).1 hkT
  have he'pos : 0 < e' := by
    by_contra hz
    have hz' : e' = 0 := by omega
    obtain ⟨i0⟩ : Nonempty (Fin (m - 1)) := ⟨⟨0, by omega⟩⟩
    set x : Fin r := ((eq.symm i0 : T.erase k) : Fin r) with hx
    have hxT := heT i0
    have hxk := hek i0
    have hgk : g k = Polynomial.C ((g k).coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hz'
    have hgx : g x = Polynomial.C ((g x).coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero (by have := hkmax x hxT; omega)
    have hak : (g k).coeff 0 ≠ 0 := by
      intro h0; apply hgne k hkT; rw [hgk, h0]; simp
    have hax : (g x).coeff 0 ≠ 0 := by
      intro h0; apply hgne x hxT; rw [hgx, h0]; simp
    have := LinearIndependent.pair_iff.1 (hna k x hxk.symm) ((g x).coeff 0) (-((g k).coeff 0))
      (by
        try simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [hg1 k hkT, hg1 x hxT, hgk, hgx]
        simp [Polynomial.smul_eq_C_mul]; ring)
    exact hax this.1
  have hnu : ∀ i : Fin (m - 1), numDistinctRoots (h i) ≤ e' := by
    intro i
    refine (nu_le _ (hcne i) _ d hd0).trans ?_
    exact hkmax _ (heT i)
  have hgcdh : ∀ q : Polynomial F, (∀ i, q ∣ h i) → IsUnit q := by
      intro q hq
      by_contra hqu
      obtain ⟨π, hπ, hπq⟩ := WfDvdMonoid.exists_irreducible_factor hqu
        (by
          intro h0
          subst h0
          have := hq ⟨0, by omega⟩
          simp only [zero_dvd_iff, h, smul_eq_zero] at this
          rcases this with h' | h'
          · exact hcne _ h'
          · exact hgne _ (heT _) (pow_eq_zero_iff hd0 |>.1 h'))
      have hπp : Prime π := hπ.prime
      have hdivh : ∀ i, π ∣ h i := fun i => hπq.trans (hq i)
      have hdiv1 : π ∣ g k ^ d := by
        have : π ∣ (-c k) • g k ^ d := by rw [← hsumh]; exact Finset.dvd_sum (fun i _ => hdivh i)
        rw [Polynomial.smul_eq_C_mul] at this
        rcases hπp.dvd_or_dvd this with h' | h'
        · exfalso
          exact hπ.not_isUnit (isUnit_of_dvd_unit h' (Polynomial.isUnit_C.2 (by simpa using hck)))
        · exact h'
      have hdivT : ∀ x ∈ T, π ∣ g x := by
        intro x hx
        by_cases hxk : x = k
        · rw [hxk]; exact hπp.dvd_of_dvd_pow hdiv1
        · have hxE : x ∈ T.erase k := Finset.mem_erase.2 ⟨hxk, hx⟩
          have := hdivh (eq ⟨x, hxE⟩)
          simp only [h, Equiv.symm_apply_apply] at this
          rw [Polynomial.smul_eq_C_mul] at this
          rcases hπp.dvd_or_dvd this with h' | h'
          · exfalso
            exact hπ.not_isUnit (isUnit_of_dvd_unit h' (Polynomial.isUnit_C.2
              (by simpa using ((hmemT x).1 hx))))
          · exact hπp.dvd_of_dvd_pow h'
      have : π ∣ T.gcd g := Finset.dvd_gcd hdivT
      rw [hg2] at this
      exact hπ.not_isUnit (isUnit_of_dvd_one this)

  have hli : LinearIndependent F h := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    by_contra hcon
    push Not at hcon
    obtain ⟨i0, hi0⟩ := hcon
    let c' : Fin r → F := fun x => if hx : x ∈ T.erase k then a (eq ⟨x, hx⟩) * c x else 0
    have hterm : ∀ i : Fin (m - 1), c' (eq.symm i : T.erase k) • f (eq.symm i : T.erase k) ^ d
        = P ^ d * (a i • h i) := by
      intro i
      have hx := (eq.symm i).2
      have hc'x : c' (eq.symm i : T.erase k) = a i * c (eq.symm i : T.erase k) := by
        simp only [c', dif_pos hx]
        simp
      rw [hc'x, hg1 _ (heT i)]
      simp only [h, Polynomial.smul_eq_C_mul, mul_pow, map_mul]
      ring
    have hc'sum : ∑ i, c' i • f i ^ d = 0 := by
      have h1 : ∀ x, c' x • f x ^ d = if x ∈ T.erase k then c' x • f x ^ d else 0 := by
        intro x
        by_cases hx : x ∈ T.erase k
        · rw [if_pos hx]
        · have : c' x = 0 := dif_neg hx
          rw [if_neg hx, this, zero_smul]
      rw [Finset.sum_congr rfl (fun x _ => h1 x)]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
        ← Finset.sum_coe_sort (T.erase k), ← Equiv.sum_comp eq.symm,
        Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum, ha, mul_zero]
    have hx0 : ((eq.symm i0 : T.erase k) : Fin r) ∈ T.erase k := (eq.symm i0).2
    have hc'ne : ∃ x, c' x ≠ 0 := by
      refine ⟨((eq.symm i0 : T.erase k) : Fin r), ?_⟩
      have : c' (eq.symm i0 : T.erase k) = a i0 * c (eq.symm i0 : T.erase k) := by
        simp only [c', dif_pos hx0]
        simp
      rw [this]
      exact mul_ne_zero hi0 (hcne i0)
    have hle := hmin c' hc'sum hc'ne
    have hsub : Finset.univ.filter (fun i => c' i ≠ 0) ⊆ T.erase k := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      by_contra hxU; apply hx; exact dif_neg hxU
    have h1 := Finset.card_le_card hsub
    rw [hEcard] at h1
    omega
  let f' : Fin (m - 1 + 1) → Polynomial F :=
    Fin.snoc (α := fun _ => Polynomial F) h (c k • g k ^ d)
  have hf'c : ∀ i : Fin (m - 1), f' i.castSucc = h i := fun i => by simp [f']
  have hf'l : f' (Fin.last (m - 1)) = c k • g k ^ d := by simp [f']
  have hsum' : ∑ i, f' i = 0 := by
    rw [Fin.sum_univ_castSucc, hf'l]
    simp only [hf'c]
    rw [hsumh, neg_smul]; simp
  have hdeg' : ∀ i, (f' i).natDegree ≤ d * e' := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [hf'l, natDegree_smul_pow _ hck]
    · rw [hf'c]
      show (c _ • g _ ^ d).natDegree ≤ _
      rw [natDegree_smul_pow _ (hcne i)]
      exact Nat.mul_le_mul_left _ (hkmax _ (heT i))
  have hgcd' : ∀ q : Polynomial F, (∀ i, q ∣ f' i) → IsUnit q := fun q hq =>
    hgcdh q (fun i => by rw [← hf'c i]; exact hq _)
  have hchar' : ringChar F = 0 ∨ d * e' < ringChar F := by
    rcases hchar with h0 | h0
    · exact Or.inl h0
    · right
      refine lt_of_le_of_lt ?_ h0
      have hf : e' ≤ δ := by
        refine le_trans ?_ (hdeg k)
        rw [he']
        refine Polynomial.natDegree_le_of_dvd ⟨P, ?_⟩ (hfne k)
        rw [hg1 k hkT]; ring
      calc d * e' ≤ d * δ := Nat.mul_le_mul le_rfl hf
        _ ≤ (r - 1) * d * δ := by
          have : 1 ≤ r - 1 := by omega
          nlinarith [Nat.zero_le (d * δ)]
  have hli' : LinearIndependent F (fun i : Fin (m - 1) => f' i.castSucc) := by
    have : (fun i : Fin (m - 1) => f' i.castSucc) = h := funext hf'c
    rw [this]; exact hli
  have hmain := DevAbc.indep_core (m - 1) f' hsum' hgcd' (d * e') hdeg' hchar' hli'
  rw [hf'l, natDegree_smul_pow _ hck] at hmain
  have hν : ∑ i, numDistinctRoots (f' i) ≤ m * e' := by
    rw [Fin.sum_univ_castSucc, hf'l]
    simp only [hf'c]
    have h1 : ∑ i : Fin (m - 1), numDistinctRoots (h i) ≤ (m - 1) * e' := by
      calc ∑ i : Fin (m - 1), numDistinctRoots (h i) ≤ ∑ _i : Fin (m - 1), e' :=
            Finset.sum_le_sum (fun i _ => hnu i)
        _ = (m - 1) * e' := by simp
    have h2 : numDistinctRoots (c k • g k ^ d) ≤ e' := nu_le _ hck _ d hd0
    have : m * e' = (m - 1) * e' + e' := by
      obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [hm']; simp; ring
    omega
  have h5 : (m - 1) ^ 2 ≤ d + 1 := (Nat.pow_le_pow_left (by omega) 2).trans hrd
  have h3 : d * e' + ∑ j : Fin (m - 1), (j : ℕ) ≤ (m - 2) * (m * e') := by
    refine hmain.trans ?_
    have : m - 1 - 1 = m - 2 := by omega
    rw [this]
    exact Nat.mul_le_mul_left _ hν
  by_cases hm3 : m = 2
  · have h0 : m - 2 = 0 := by omega
    rw [h0, zero_mul] at h3
    have := Nat.mul_pos (show 0 < d by omega) he'pos
    omega
  · have hS : 1 ≤ ∑ j : Fin (m - 1), (j : ℕ) := by
      have h2' : 2 ≤ m - 1 := by omega
      calc 1 = ((⟨1, by omega⟩ : Fin (m - 1)) : ℕ) := rfl
        _ ≤ _ := Finset.single_le_sum (f := fun j : Fin (m - 1) => (j : ℕ)) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ _)
    have h4 : d < (m - 2) * m := by
      have : d * e' < ((m - 2) * m) * e' := by nlinarith [h3, hS]
      exact Nat.lt_of_mul_lt_mul_right this
    obtain ⟨m', hm'⟩ : ∃ m', m = m' + 3 := ⟨m - 3, by omega⟩
    rw [hm'] at h4 h5
    simp at h4 h5
    nlinarith

end SumsHighPowers.PITLifting.Dev210

namespace SumsHighPowers.PITLifting

open Classical in
theorem chk_theorem_2_10 {F : Type*} [Field F] (r d δ : ℕ) (hr : 3 ≤ r)
    (hchar : ringChar F = 0 ∨ (r - 1) * d * δ < ringChar F)
    (f : Fin r → Polynomial F) (hna : PairwiseNonAssociate (F := F) f)
    (hdeg : ∀ i, (f i).natDegree ≤ δ)
    (hrd : (r - 1) ^ 2 ≤ d + 1) :
    LinearIndependent F (fun i => f i ^ d) := by
  by_contra hLI
  rw [Fintype.not_linearIndependent_iff] at hLI
  have hex : ∃ n, ∃ c : Fin r → F, ∑ i, c i • f i ^ d = 0 ∧ (∃ i, c i ≠ 0) ∧
      (Finset.univ.filter (fun i => c i ≠ 0)).card = n := by
    obtain ⟨c, h1, h2⟩ := hLI
    exact ⟨_, c, h1, h2, rfl⟩
  obtain ⟨c, hc1, hc2, hc3⟩ := Nat.find_spec hex
  refine Dev210.core r d δ hr hchar f hna hdeg hrd c hc1 ?_ hc2
  intro c' h1 h2
  rw [hc3]
  exact Nat.find_min' hex ⟨c', h1, h2, rfl⟩

end SumsHighPowers.PITLifting
end

theorem solution : type_of% @SumsHighPowers.PITLifting.chk_theorem_2_10 := @SumsHighPowers.PITLifting.chk_theorem_2_10
