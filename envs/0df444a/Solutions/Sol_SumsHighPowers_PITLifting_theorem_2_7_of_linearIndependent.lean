-- Prove2me | solution 1 for SumsHighPowers.PITLifting.theorem_2_7_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:15:22.571174+00:00
-- url     : https://prove2.me/submissions/260451d4-b9f2-4cc1-b5aa-fd44e4848892

import Mathlib
import Definitions.Def_SumsHighPowers_PITLifting_numDistinctRoots

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
open Polynomial

namespace SumsHighPowers.PITLifting.Dev27

open SumsHighPowers.PITLifting

theorem numDistinctRoots_neg {F : Type*} [Field F] (p : F[X]) :
    numDistinctRoots (-p) = numDistinctRoots p := by
  unfold numDistinctRoots
  rw [Polynomial.map_neg, Polynomial.roots_neg]

/-- The linearly independent case, with `n = r - 1` summands. -/
theorem indep_case {F : Type*} [Field F] (D n : ℕ) (hn : 1 ≤ n)
    (hchar : ringChar F = 0 ∨ n * D < ringChar F)
    (h₁ : F[X]) (h : Fin n → F[X])
    (hsum : ∑ i, h i = h₁)
    (hgcd : ∀ q : F[X], (∀ i, q ∣ h i) → IsUnit q)
    (hdeg₁ : h₁.natDegree ≤ D) (hdeg : ∀ i, (h i).natDegree ≤ D)
    (hnonconst : 0 < h₁.natDegree ∨ ∃ i, 0 < (h i).natDegree)
    (hli : LinearIndependent F h) :
    h₁.natDegree < (n - 1) * (numDistinctRoots h₁ + ∑ i, numDistinctRoots (h i)) := by
  classical
  -- n = 1 is vacuous: h 0 is a unit, so everything is constant
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · exfalso
    obtain rfl : n = 1 := by omega
    have hu : IsUnit (h 0) := hgcd (h 0) (fun i => by rw [Subsingleton.elim i 0])
    have h0 : (h 0).natDegree = 0 := natDegree_eq_zero_of_isUnit hu
    have h1e : h₁ = h 0 := by rw [← hsum, Fin.sum_univ_one]
    rcases hnonconst with hc | ⟨i, hi⟩
    · rw [h1e, h0] at hc; exact lt_irrefl _ hc
    · rw [Subsingleton.elim i 0, h0] at hi; exact lt_irrefl _ hi
  set f : Fin (n + 1) → F[X] := Fin.snoc h (-h₁) with hf
  have hfc : ∀ i : Fin n, f i.castSucc = h i := fun i => by simp [hf]
  have hfl : f (Fin.last n) = -h₁ := by simp [hf]
  have hfsum : ∑ i, f i = 0 := by
    rw [Fin.sum_univ_castSucc, hfl]
    simp only [hfc, hsum, add_neg_cancel]
  have hfgcd : ∀ q : F[X], (∀ i, q ∣ f i) → IsUnit q := fun q hq =>
    hgcd q (fun i => by rw [← hfc i]; exact hq _)
  have hfdeg : ∀ i, (f i).natDegree ≤ D := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hfl, natDegree_neg]; exact hdeg₁
    · rw [hfc]; exact hdeg j
  have hchar' : ringChar F = 0 ∨ D < ringChar F := by
    rcases hchar with h0 | hp
    · exact Or.inl h0
    · right
      by_cases hD : D = 0
      · subst hD; omega
      · have : D ≤ n * D := Nat.le_mul_of_pos_left D (by omega)
        omega
  have hli' : LinearIndependent F (fun i : Fin n => f i.castSucc) := by
    have : (fun i : Fin n => f i.castSucc) = h := funext hfc
    rw [this]; exact hli
  have key := DevAbc.indep_core n f hfsum hfgcd D hfdeg hchar' hli'
  rw [hfl, natDegree_neg, Fin.sum_univ_castSucc, hfl, numDistinctRoots_neg] at key
  simp only [hfc] at key
  have hpos : 1 ≤ ∑ j : Fin n, (j : ℕ) := by
    have := Finset.single_le_sum (f := fun j : Fin n => (j : ℕ)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (⟨1, by omega⟩ : Fin n))
    simpa using this
  have : numDistinctRoots h₁ + ∑ i, numDistinctRoots (h i) =
      ∑ i, numDistinctRoots (h i) + numDistinctRoots h₁ := by ring
  rw [this]
  omega

end SumsHighPowers.PITLifting.Dev27

namespace SumsHighPowers.PITLifting

open Polynomial

theorem chk_theorem_2_7_of_linearIndependent {F : Type*} [Field F] (D r : ℕ) (hr : 2 ≤ r)
    (hchar : ringChar F = 0 ∨ (r - 1) * D < ringChar F)
    (h₁ : Polynomial F) (h : Fin (r - 1) → Polynomial F)
    (hsum : ∑ i, h i = h₁)
    (hgcd : ∀ q : Polynomial F, (∀ i, q ∣ h i) → IsUnit q)
    (hdeg₁ : h₁.natDegree ≤ D) (hdeg : ∀ i, (h i).natDegree ≤ D)
    (hnonconst : 0 < h₁.natDegree ∨ ∃ i, 0 < (h i).natDegree)
    (hsubsum : ∀ T : Finset (Fin (r - 1)), T.Nonempty → ∑ i ∈ T, h i ≠ 0)
    (hli : LinearIndependent F h) :
    h₁.natDegree < (r - 2) * (numDistinctRoots h₁ + ∑ i, numDistinctRoots (h i)) := by
  have hr2 : r - 2 = (r - 1) - 1 := by omega
  rw [hr2]
  exact Dev27.indep_case D (r - 1) (by omega) hchar h₁ h hsum hgcd hdeg₁ hdeg hnonconst hli

end SumsHighPowers.PITLifting
end

theorem solution : type_of% @SumsHighPowers.PITLifting.chk_theorem_2_7_of_linearIndependent := @SumsHighPowers.PITLifting.chk_theorem_2_7_of_linearIndependent
