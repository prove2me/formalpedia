-- Prove2me | solution 1 for Polynomial.exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9783dbb1-b98e-54e2-a01e-b4cd8e391710

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete

set_option autoImplicit false

p2m_open "Polynomial P2MW.S_Polynomial_exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete.Polynomial"

namespace Polynomial
p2m_export "Polynomial" "C X coeff_natDegree resultant_map_map natDegree_mul leadingCoeff coeff degree_le_iff_coeff_zero isUnit_resultant_iff_isCoprime unique lifts_and_natDegree_eq_and_monic coeff_eq_zero_of_degree_lt ker_mapRingHom degree map_divByMonic monic_one map_id degree_eq_bot zero_divByMonic degree_sub_le map_map coeff_sub nontrivial_iff degree_add_le map resultant comp_assoc Monic comp roots algebra coe_mapRingHom zero_modByMonic map_modByMonic coeff_zero natDegree monic_of_degree_le eq_of_monic_of_dvd_of_natDegree_le degree_modByMonic_lt natDegree_map degree_sub_lt natDegree_eq_of_degree_eq mem_lifts_of_surjective modByMonic_add_div div resultant_add_right_deg finsetSum_coeff mod ext mapRingHom degree_eq_natDegree coeff_C_mul_X_pow degree_add_eq_left_of_degree_lt natDegree_map_le ring lifts degree_mul degree_zero"
p2m_open "Polynomial"

namespace HenselFactorisation

variable {R : Type*} [CommRing R]

theorem mem_mapC_iff {J : Ideal R} {p : R[X]} :
    p ∈ (J.map C : Ideal R[X]) ↔ p.map (Ideal.Quotient.mk J) = 0 := by
  have : (J.map C : Ideal R[X]) = RingHom.ker (mapRingHom (Ideal.Quotient.mk J)) := by
    rw [ker_mapRingHom, Ideal.mk_ker]
  rw [this, RingHom.mem_ker, coe_mapRingHom]

theorem map_eq_map_iff {J : Ideal R} {p q : R[X]} :
    p.map (Ideal.Quotient.mk J) = q.map (Ideal.Quotient.mk J) ↔ p - q ∈ (J.map C : Ideal R[X]) := by
  rw [mem_mapC_iff, Polynomial.map_sub, sub_eq_zero]

theorem mul_mem_mapC {J₁ J₂ : Ideal R} {p q : R[X]} (hp : p ∈ (J₁.map C : Ideal R[X]))
    (hq : q ∈ (J₂.map C : Ideal R[X])) : p * q ∈ ((J₁ * J₂).map C : Ideal R[X]) := by
  rw [Ideal.map_mul]
  exact Ideal.mul_mem_mul hp hq

theorem mapC_mono {J₁ J₂ : Ideal R} (h : J₁ ≤ J₂) : (J₁.map C : Ideal R[X]) ≤ J₂.map C :=
  Ideal.map_mono h

theorem mapC_pow_mono {I : Ideal R} {m n : ℕ} (h : m ≤ n) :
    ((I ^ n).map C : Ideal R[X]) ≤ (I ^ m).map C :=
  mapC_mono (Ideal.pow_le_pow_right h)

theorem coeff_mem_of_mem_mapC {J : Ideal R} {p : R[X]} (hp : p ∈ (J.map C : Ideal R[X])) (n : ℕ) :
    p.coeff n ∈ J :=
  Ideal.mem_map_C_iff.mp hp n

theorem mem_mapC_of_coeff_mem {J : Ideal R} {p : R[X]} (hp : ∀ n, p.coeff n ∈ J) :
    p ∈ (J.map C : Ideal R[X]) :=
  Ideal.mem_map_C_iff.mpr hp

theorem smodEq_iff_sub_mem {J : Ideal R} {x y : R} :
    x ≡ y [SMOD (J • ⊤ : Submodule R R)] ↔ x - y ∈ J := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem isCoprime_of_isCoprime_map {I : Ideal R} (hI : I ≤ (⊥ : Ideal R).jacobson) {g h : R[X]}
    (hg : g.Monic) (hcop : IsCoprime (g.map (Ideal.Quotient.mk I)) (h.map (Ideal.Quotient.mk I))) :
    IsCoprime g h := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨1, 0, Subsingleton.elim _ _⟩
  have hI' : I ≠ ⊤ := by
    rintro rfl
    have h1 : (⊥ : Ideal R).jacobson = ⊤ := top_le_iff.mp hI
    rw [Ideal.jacobson_eq_top_iff] at h1
    exact bot_ne_top h1
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI'
  haveI := isLocalHom_of_le_jacobson_bot I hI
  set π := Ideal.Quotient.mk I
  have hdeg : (g.map π).natDegree = g.natDegree := hg.natDegree_map π

  have hunit : IsUnit ((g.map π).resultant (h.map π) g.natDegree h.natDegree) := by
    have key := (isUnit_resultant_iff_isCoprime (hg.map π)).mpr hcop

    obtain ⟨k, hk⟩ : ∃ k, h.natDegree = (h.map π).natDegree + k :=
      ⟨h.natDegree - (h.map π).natDegree, (Nat.add_sub_cancel' natDegree_map_le).symm⟩
    rw [hk, resultant_add_right_deg _ _ _ _ _ le_rfl, ← hdeg]
    have hc : (g.map π).coeff (g.map π).natDegree = 1 := (hg.map π).coeff_natDegree
    rw [hc, one_pow, one_mul]
    exact key
  rw [resultant_map_map] at hunit
  exact (isUnit_resultant_iff_isCoprime hg).mp (IsUnit.of_map π _ hunit)

section Solver

variable (g h a b : R[X])

noncomputable def solU (e : R[X]) : R[X] := (e * b) %ₘ g

noncomputable def solV (e : R[X]) : R[X] := e * a + (e * b /ₘ g) * h

variable {g h a b}

theorem solU_mul_add_solV_mul (hab : a * g + b * h = 1) (e : R[X]) :
    solU g b e * h + solV g h a b e * g = e := by
  have hdiv := modByMonic_add_div (e * b) g
  unfold solU solV
  linear_combination h * hdiv + e * hab

theorem degree_solU_lt [Nontrivial R] (hg : g.Monic) (e : R[X]) : (solU g b e).degree < g.degree :=
  degree_modByMonic_lt _ hg

theorem degree_solV_lt [Nontrivial R] (hg : g.Monic) (hh : h.Monic) (hab : a * g + b * h = 1)
    {e : R[X]} (he : e.degree < (g * h).degree) : (solV g h a b e).degree < h.degree := by
  have key : solV g h a b e * g = e - solU g b e * h := by
    linear_combination solU_mul_add_solV_mul hab e
  by_contra hV
  rw [not_lt] at hV
  have h1 : (solV g h a b e * g).degree = (solV g h a b e).degree + g.degree := hg.degree_mul
  have h2 : (g * h).degree = g.degree + h.degree := hh.degree_mul
  have hUh : (solU g b e * h).degree < (g * h).degree := by
    rw [hh.degree_mul, h2]
    exact WithBot.add_lt_add_right (degree_eq_bot.not.mpr hh.ne_zero) (degree_solU_lt hg e)
  have h3 : (e - solU g b e * h).degree < (g * h).degree :=
    (degree_sub_le _ _).trans_lt (max_lt he hUh)
  have h4 : (g * h).degree ≤ (solV g h a b e * g).degree := by
    rw [h1, h2, add_comm g.degree]
    exact add_le_add_left hV _
  rw [key] at h4
  exact lt_irrefl _ (h3.trans_le h4)

theorem solU_mem {J : Ideal R} (hg : g.Monic) {e : R[X]} (he : e ∈ (J.map C : Ideal R[X])) :
    solU g b e ∈ (J.map C : Ideal R[X]) := by
  rw [mem_mapC_iff] at he ⊢
  unfold solU
  rw [map_modByMonic _ hg, Polynomial.map_mul, he, zero_mul, zero_modByMonic]

theorem solV_mem {J : Ideal R} (hg : g.Monic) {e : R[X]} (he : e ∈ (J.map C : Ideal R[X])) :
    solV g h a b e ∈ (J.map C : Ideal R[X]) := by
  rw [mem_mapC_iff] at he ⊢
  unfold solV
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, map_divByMonic _ hg,
    Polynomial.map_mul, he, zero_mul, zero_mul, zero_divByMonic, zero_mul, add_zero]

end Solver

section Iteration

variable (F g h a b : R[X])

noncomputable def step (q : R[X] × R[X]) : R[X] × R[X] :=
  (q.1 + solU g b (F - q.1 * q.2), q.2 + solV g h a b (F - q.1 * q.2))

noncomputable def seq (k : ℕ) : R[X] × R[X] := (step F g h a b)^[k] (g, h)

@[scoped simp] theorem seq_zero : seq F g h a b 0 = (g, h) := rfl

theorem seq_succ (k : ℕ) : seq F g h a b (k + 1) = step F g h a b (seq F g h a b k) :=
  Function.iterate_succ_apply' _ _ _

structure Inv (I : Ideal R) (k : ℕ) (q : R[X] × R[X]) : Prop where
  fst_sub_mem : q.1 - g ∈ (I.map C : Ideal R[X])
  snd_sub_mem : q.2 - h ∈ (I.map C : Ideal R[X])
  degree_fst_sub_lt : (q.1 - g).degree < g.degree
  degree_snd_sub_lt : (q.2 - h).degree < h.degree
  err_mem : F - q.1 * q.2 ∈ ((I ^ (k + 1)).map C : Ideal R[X])

variable {F g h a b}
variable {I : Ideal R}

theorem Inv.monic_fst {k : ℕ} {q : R[X] × R[X]} (hq : Inv F g h I k q) (hg : g.Monic) : q.1.Monic := by
  have : q.1 = g + (q.1 - g) := by ring
  rw [this]
  exact hg.add_of_left hq.degree_fst_sub_lt

theorem Inv.monic_snd {k : ℕ} {q : R[X] × R[X]} (hq : Inv F g h I k q) (hh : h.Monic) : q.2.Monic := by
  have : q.2 = h + (q.2 - h) := by ring
  rw [this]
  exact hh.add_of_left hq.degree_snd_sub_lt

theorem Inv.degree_fst {k : ℕ} {q : R[X] × R[X]} (hq : Inv F g h I k q) : q.1.degree = g.degree := by
  have : q.1 = g + (q.1 - g) := by ring
  rw [this]
  exact degree_add_eq_left_of_degree_lt hq.degree_fst_sub_lt

theorem Inv.degree_snd {k : ℕ} {q : R[X] × R[X]} (hq : Inv F g h I k q) : q.2.degree = h.degree := by
  have : q.2 = h + (q.2 - h) := by ring
  rw [this]
  exact degree_add_eq_left_of_degree_lt hq.degree_snd_sub_lt

theorem Inv.degree_err_lt [Nontrivial R] {k : ℕ} {q : R[X] × R[X]} (hq : Inv F g h I k q)
    (hF : F.Monic) (hg : g.Monic) (hh : h.Monic) (hN : F.degree = (g * h).degree) :
    (F - q.1 * q.2).degree < (g * h).degree := by
  have hGH : (q.1 * q.2).Monic := (hq.monic_fst hg).mul (hq.monic_snd hh)
  have hdGH : (q.1 * q.2).degree = (g * h).degree := by
    rw [(hq.monic_snd hh).degree_mul, hh.degree_mul, hq.degree_fst, hq.degree_snd]
  rw [← hN]
  refine degree_sub_lt (hN.trans hdGH.symm) hF.ne_zero ?_
  rw [hF.leadingCoeff, hGH.leadingCoeff]

end Iteration

section Invariant

variable {F g h a b : R[X]} {I : Ideal R}

theorem inv_zero (hg : g.Monic) (hh : h.Monic) [Nontrivial R]
    (hFgh : F - g * h ∈ (I.map C : Ideal R[X])) : Inv F g h I 0 (seq F g h a b 0) where
  fst_sub_mem := by simp
  snd_sub_mem := by simp
  degree_fst_sub_lt := by
    simp only [seq_zero, sub_self, degree_zero]
    exact bot_lt_iff_ne_bot.mpr (degree_eq_bot.not.mpr hg.ne_zero)
  degree_snd_sub_lt := by
    simp only [seq_zero, sub_self, degree_zero]
    exact bot_lt_iff_ne_bot.mpr (degree_eq_bot.not.mpr hh.ne_zero)
  err_mem := by simpa using hFgh

theorem err_step (hab : a * g + b * h = 1) (q : R[X] × R[X]) :
    F - (step F g h a b q).1 * (step F g h a b q).2 =
      -((q.1 - g) * solV g h a b (F - q.1 * q.2) + solU g b (F - q.1 * q.2) * (q.2 - h)
        + solU g b (F - q.1 * q.2) * solV g h a b (F - q.1 * q.2)) := by
  have key := solU_mul_add_solV_mul (g := g) (h := h) hab (F - q.1 * q.2)
  simp only [step]
  linear_combination (-1 : R[X]) * key

theorem inv_succ [Nontrivial R] (hF : F.Monic) (hg : g.Monic) (hh : h.Monic)
    (hN : F.degree = (g * h).degree) (hab : a * g + b * h = 1) {k : ℕ} {q : R[X] × R[X]}
    (hq : Inv F g h I k q) : Inv F g h I (k + 1) (step F g h a b q) := by
  have he : F - q.1 * q.2 ∈ ((I ^ (k + 1)).map C : Ideal R[X]) := hq.err_mem
  have hu : solU g b (F - q.1 * q.2) ∈ ((I ^ (k + 1)).map C : Ideal R[X]) := solU_mem hg he
  have hv : solV g h a b (F - q.1 * q.2) ∈ ((I ^ (k + 1)).map C : Ideal R[X]) := solV_mem hg he
  have hI1 : ((I ^ (k + 1)).map C : Ideal R[X]) ≤ I.map C := by
    simpa using (mapC_pow_mono (I := I) (Nat.le_add_left 1 k))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : (step F g h a b q).1 - g = (q.1 - g) + solU g b (F - q.1 * q.2) := by
      simp only [step]; ring
    rw [this]
    exact add_mem hq.fst_sub_mem (hI1 hu)
  · have : (step F g h a b q).2 - h = (q.2 - h) + solV g h a b (F - q.1 * q.2) := by
      simp only [step]; ring
    rw [this]
    exact add_mem hq.snd_sub_mem (hI1 hv)
  · have : (step F g h a b q).1 - g = (q.1 - g) + solU g b (F - q.1 * q.2) := by
      simp only [step]; ring
    rw [this]
    exact (degree_add_le _ _).trans_lt (max_lt hq.degree_fst_sub_lt (degree_solU_lt hg _))
  · have : (step F g h a b q).2 - h = (q.2 - h) + solV g h a b (F - q.1 * q.2) := by
      simp only [step]; ring
    rw [this]
    exact (degree_add_le _ _).trans_lt
      (max_lt hq.degree_snd_sub_lt (degree_solV_lt hg hh hab (hq.degree_err_lt hF hg hh hN)))
  · rw [err_step hab]
    refine neg_mem (add_mem (add_mem ?_ ?_) ?_)
    · have := mul_mem_mapC hq.fst_sub_mem hv
      rwa [← pow_succ'] at this
    · have := mul_mem_mapC hu hq.snd_sub_mem
      rwa [← pow_succ] at this
    · have := mul_mem_mapC hu hv
      rw [← pow_add] at this
      exact mapC_pow_mono (by omega) this

theorem inv_seq [Nontrivial R] (hF : F.Monic) (hg : g.Monic) (hh : h.Monic)
    (hN : F.degree = (g * h).degree) (hab : a * g + b * h = 1)
    (hFgh : F - g * h ∈ (I.map C : Ideal R[X])) (k : ℕ) : Inv F g h I k (seq F g h a b k) := by
  induction k with
  | zero => exact inv_zero hg hh hFgh
  | succ k ih =>
    rw [seq_succ]
    exact inv_succ hF hg hh hN hab ih

theorem seq_sub_seq_mem [Nontrivial R] (hF : F.Monic) (hg : g.Monic) (hh : h.Monic)
    (hN : F.degree = (g * h).degree) (hab : a * g + b * h = 1)
    (hFgh : F - g * h ∈ (I.map C : Ideal R[X])) {m n : ℕ} (hmn : m ≤ n) :
    (seq F g h a b n).1 - (seq F g h a b m).1 ∈ ((I ^ (m + 1)).map C : Ideal R[X]) ∧
      (seq F g h a b n).2 - (seq F g h a b m).2 ∈ ((I ^ (m + 1)).map C : Ideal R[X]) := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have hq := inv_seq hF hg hh hN hab hFgh n
    have he := hq.err_mem
    have hle : ((I ^ (n + 1)).map C : Ideal R[X]) ≤ (I ^ (m + 1)).map C := mapC_pow_mono (by omega)
    constructor
    · have : (seq F g h a b (n + 1)).1 - (seq F g h a b m).1 =
          solU g b (F - (seq F g h a b n).1 * (seq F g h a b n).2)
            + ((seq F g h a b n).1 - (seq F g h a b m).1) := by
        rw [seq_succ]; simp only [step]; ring
      rw [this]
      exact add_mem (hle (solU_mem hg he)) ih.1
    · have : (seq F g h a b (n + 1)).2 - (seq F g h a b m).2 =
          solV g h a b (F - (seq F g h a b n).1 * (seq F g h a b n).2)
            + ((seq F g h a b n).2 - (seq F g h a b m).2) := by
        rw [seq_succ]; simp only [step]; ring
      rw [this]
      exact add_mem (hle (solV_mem hg he)) ih.2

end Invariant

section Limit

variable {I : Ideal R}

noncomputable def limPoly (L : ℕ → R) (d : ℕ) : R[X] := ∑ i ∈ Finset.range (d + 1), C (L i) * X ^ i

theorem coeff_limPoly (L : ℕ → R) (d i : ℕ) :
    (limPoly L d).coeff i = if i ≤ d then L i else 0 := by
  simp only [limPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range (d + 1)) i (fun j => L j)]
  simp

theorem exists_limit [IsPrecomplete I R] (P : ℕ → R[X]) (d : ℕ) (hd : ∀ n, (P n).degree ≤ d)
    (hP : ∀ m n, m ≤ n → P n - P m ∈ ((I ^ (m + 1)).map C : Ideal R[X])) :
    ∃ Q : R[X], Q.degree ≤ d ∧ ∀ n, P n - Q ∈ ((I ^ n).map C : Ideal R[X]) := by

  have hlim : ∀ i, ∃ L : R, ∀ n, (P n).coeff i - L ∈ I ^ n := by
    intro i
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun n => (P n).coeff i) (fun {m n} hmn => by
      rw [smodEq_iff_sub_mem]
      have := coeff_mem_of_mem_mapC (hP m n hmn) i
      rw [coeff_sub] at this
      have h' : (P m).coeff i - (P n).coeff i = -((P n).coeff i - (P m).coeff i) := by ring
      rw [h']
      exact neg_mem (Ideal.pow_le_pow_right (Nat.le_succ m) this))
    exact ⟨L, fun n => (smodEq_iff_sub_mem.mp (hL n))⟩
  choose L hL using hlim
  refine ⟨limPoly L d, ?_, fun n => mem_mapC_of_coeff_mem fun i => ?_⟩
  · rw [degree_le_iff_coeff_zero]
    intro i hi
    rw [coeff_limPoly, if_neg]
    exact_mod_cast not_le.mpr hi
  · rw [coeff_sub, coeff_limPoly]
    split_ifs with hi
    · exact hL i n
    · have : (P n).coeff i = 0 := by
        apply coeff_eq_zero_of_degree_lt
        exact (hd n).trans_lt (by exact_mod_cast not_le.mp hi)
      rw [this, sub_zero]
      exact zero_mem _

theorem eq_zero_of_forall_mem [IsHausdorff I R] {p : R[X]}
    (hp : ∀ n, p ∈ ((I ^ n).map C : Ideal R[X])) : p = 0 := by
  ext i
  rw [coeff_zero]
  refine IsHausdorff.haus' (I := I) _ fun n => ?_
  rw [smodEq_iff_sub_mem, sub_zero]
  exact coeff_mem_of_mem_mapC (hp n) i

end Limit

section Main

variable {I : Ideal R}

theorem exists_lift [IsAdicComplete I R] [Nontrivial R] {F g h a b : R[X]}
    (hF : F.Monic) (hg : g.Monic) (hh : h.Monic) (hN : F.degree = (g * h).degree)
    (hab : a * g + b * h = 1) (hFgh : F - g * h ∈ (I.map C : Ideal R[X])) :
    ∃ G H : R[X], G.Monic ∧ H.Monic ∧ G * H = F ∧ G - g ∈ (I.map C : Ideal R[X]) ∧
      H - h ∈ (I.map C : Ideal R[X]) := by
  have hinv := inv_seq (a := a) (b := b) hF hg hh hN hab hFgh
  have hcau := fun m n (hmn : m ≤ n) =>
    seq_sub_seq_mem (a := a) (b := b) hF hg hh hN hab hFgh hmn
  obtain ⟨G, hGd, hG⟩ := exists_limit (I := I) (fun n => (seq F g h a b n).1) g.natDegree
    (fun n => by rw [(hinv n).degree_fst, degree_eq_natDegree hg.ne_zero])
    (fun m n hmn => (hcau m n hmn).1)
  obtain ⟨H, hHd, hH⟩ := exists_limit (I := I) (fun n => (seq F g h a b n).2) h.natDegree
    (fun n => by rw [(hinv n).degree_snd, degree_eq_natDegree hh.ne_zero])
    (fun m n hmn => (hcau m n hmn).2)

  have hGg : G - g ∈ (I.map C : Ideal R[X]) := by
    have h1 := hG 1
    rw [pow_one] at h1
    have : G - g = ((seq F g h a b 1).1 - g) - ((seq F g h a b 1).1 - G) := by ring
    rw [this]
    exact sub_mem (hinv 1).fst_sub_mem h1
  have hHh : H - h ∈ (I.map C : Ideal R[X]) := by
    have h1 := hH 1
    rw [pow_one] at h1
    have : H - h = ((seq F g h a b 1).2 - h) - ((seq F g h a b 1).2 - H) := by ring
    rw [this]
    exact sub_mem (hinv 1).snd_sub_mem h1

  have hGm : G.Monic := by
    refine monic_of_degree_le _ hGd ?_
    have hc : ∀ n, (1 : R) - G.coeff g.natDegree ∈ I ^ n := fun n => by
      have hmon := (hinv n).monic_fst hg
      have hnd : (seq F g h a b n).1.natDegree = g.natDegree :=
        natDegree_eq_of_degree_eq ((hinv n).degree_fst)
      have := coeff_mem_of_mem_mapC (hG n) g.natDegree
      rwa [coeff_sub, ← hnd, hmon.coeff_natDegree, hnd] at this
    have h0 : (1 : R) - G.coeff g.natDegree = 0 :=
      IsHausdorff.haus' (I := I) _ fun n => by rw [smodEq_iff_sub_mem, sub_zero]; exact hc n
    exact (sub_eq_zero.mp h0).symm
  have hHm : H.Monic := by
    refine monic_of_degree_le _ hHd ?_
    have hc : ∀ n, (1 : R) - H.coeff h.natDegree ∈ I ^ n := fun n => by
      have hmon := (hinv n).monic_snd hh
      have hnd : (seq F g h a b n).2.natDegree = h.natDegree :=
        natDegree_eq_of_degree_eq ((hinv n).degree_snd)
      have := coeff_mem_of_mem_mapC (hH n) h.natDegree
      rwa [coeff_sub, ← hnd, hmon.coeff_natDegree, hnd] at this
    have h0 : (1 : R) - H.coeff h.natDegree = 0 :=
      IsHausdorff.haus' (I := I) _ fun n => by rw [smodEq_iff_sub_mem, sub_zero]; exact hc n
    exact (sub_eq_zero.mp h0).symm

  have hGH : F - G * H = 0 := by
    refine eq_zero_of_forall_mem (I := I) fun n => ?_
    have he : F - (seq F g h a b n).1 * (seq F g h a b n).2 ∈ ((I ^ n).map C : Ideal R[X]) :=
      mapC_pow_mono (Nat.le_succ n) (hinv n).err_mem
    have : F - G * H = (F - (seq F g h a b n).1 * (seq F g h a b n).2)
        + ((seq F g h a b n).1 * ((seq F g h a b n).2 - H) + ((seq F g h a b n).1 - G) * H) := by
      ring
    rw [this]
    exact add_mem he (add_mem (Ideal.mul_mem_left _ _ (hH n)) (Ideal.mul_mem_right _ _ (hG n)))
  exact ⟨G, H, hGm, hHm, (sub_eq_zero.mp hGH).symm, hGg, hHh⟩

theorem main (I : Ideal R) [IsAdicComplete I R] {F : R[X]} (hF : F.Monic) {g₀ h₀ : (R ⧸ I)[X]}
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcop : IsCoprime g₀ h₀)
    (hF₀ : F.map (Ideal.Quotient.mk I) = g₀ * h₀) :
    ∃ g h : R[X], g.Monic ∧ h.Monic ∧ g * h = F ∧
      g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀ ∧ IsCoprime g h ∧
      ∀ g' : R[X], g'.Monic → g'.map (Ideal.Quotient.mk I) = g₀ → g' ∣ F → g' = g := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI : Subsingleton (R ⧸ I) := Ideal.Quotient.mk_surjective.subsingleton
    exact ⟨F, 1, Subsingleton.elim _ _, monic_one, mul_one F, Subsingleton.elim _ _,
      Subsingleton.elim _ _, isCoprime_one_right, fun g' _ _ _ => Subsingleton.elim _ _⟩
  have hI : I ≤ (⊥ : Ideal R).jacobson := IsAdicComplete.le_jacobson_bot I
  have hI' : I ≠ ⊤ := by
    rintro rfl
    have h1 : (⊥ : Ideal R).jacobson = ⊤ := top_le_iff.mp hI
    rw [Ideal.jacobson_eq_top_iff] at h1
    exact bot_ne_top h1
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI'
  set π := Ideal.Quotient.mk I with hπ

  obtain ⟨g, hgmap, hgdeg, hg⟩ :=
    lifts_and_natDegree_eq_and_monic (mem_lifts_of_surjective Ideal.Quotient.mk_surjective g₀) hg₀
  obtain ⟨h, hhmap, hhdeg, hh⟩ :=
    lifts_and_natDegree_eq_and_monic (mem_lifts_of_surjective Ideal.Quotient.mk_surjective h₀) hh₀

  have hcopR : IsCoprime g h :=
    isCoprime_of_isCoprime_map hI hg (by rw [hgmap, hhmap]; exact hcop)
  obtain ⟨a, b, hab⟩ := hcopR

  have hFgh : F - g * h ∈ (I.map C : Ideal R[X]) :=
    map_eq_map_iff.mp (by rw [Polynomial.map_mul, hgmap, hhmap, hF₀])
  have hN : F.degree = (g * h).degree := by
    rw [degree_eq_natDegree hF.ne_zero, degree_eq_natDegree (hg.mul hh).ne_zero, hg.natDegree_mul hh,
      hgdeg, hhdeg, ← hg₀.natDegree_mul hh₀, ← hF₀, hF.natDegree_map]
  obtain ⟨G, H, hG, hH, hGH, hGg, hHh⟩ := exists_lift hF hg hh hN hab hFgh
  have hGmap : G.map π = g₀ := by rw [← hgmap]; exact map_eq_map_iff.mpr hGg
  have hHmap : H.map π = h₀ := by rw [← hhmap]; exact map_eq_map_iff.mpr hHh
  refine ⟨G, H, hG, hH, hGH, hGmap, hHmap, ?_, ?_⟩
  · exact isCoprime_of_isCoprime_map hI hG (by rw [hGmap, hHmap]; exact hcop)
  · intro g' hg' hg'map hg'F
    have hcop' : IsCoprime g' H :=
      isCoprime_of_isCoprime_map hI hg' (by rw [hg'map, hHmap]; exact hcop)
    have hdvd : g' ∣ G := hcop'.dvd_of_dvd_mul_right (by rwa [hGH])
    have hdG : G.natDegree = g₀.natDegree := by rw [← hGmap, hG.natDegree_map]
    have hdg' : g'.natDegree = g₀.natDegree := by rw [← hg'map, hg'.natDegree_map]
    exact (eq_of_monic_of_dvd_of_natDegree_le hg' hG hdvd (by rw [hdG, hdg'])).symm

theorem main_of_surjective {S : Type*} [CommRing S] (π : R →+* S) (hπ : Function.Surjective π)
    [IsAdicComplete (RingHom.ker π) R] {F : R[X]} (hF : F.Monic) {g₀ h₀ : S[X]}
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcop : IsCoprime g₀ h₀) (hF₀ : F.map π = g₀ * h₀) :
    ∃ g h : R[X], g.Monic ∧ h.Monic ∧ g * h = F ∧ g.map π = g₀ ∧ h.map π = h₀ ∧ IsCoprime g h ∧
      ∀ g' : R[X], g'.Monic → g'.map π = g₀ → g' ∣ F → g' = g := by
  set I := RingHom.ker π
  set e : R ⧸ I ≃+* S := RingHom.quotientKerEquivOfSurjective hπ
  have he : (e : R ⧸ I →+* S).comp (Ideal.Quotient.mk I) = π :=
    RingHom.ext fun x => RingHom.quotientKerEquivOfSurjective_apply_mk hπ x
  have he' : (e.symm : S →+* R ⧸ I).comp π = Ideal.Quotient.mk I := by
    rw [← he, ← RingHom.comp_assoc]
    ext x
    simp

  have key := main I hF (hg₀.map (e.symm : S →+* R ⧸ I)) (hh₀.map (e.symm : S →+* R ⧸ I))
    (hcop.map (mapRingHom (e.symm : S →+* R ⧸ I))) (by
      rw [← he', ← Polynomial.map_map, hF₀, Polynomial.map_mul])
  obtain ⟨g, h, hg, hh, hgh, hgmap, hhmap, hcopR, huniq⟩ := key
  have back : ∀ {p : R[X]} {q : S[X]},
      p.map (Ideal.Quotient.mk I) = q.map (e.symm : S →+* R ⧸ I) → p.map π = q := by
    intro p q hpq
    have := congrArg (Polynomial.map (e : R ⧸ I →+* S)) hpq
    rw [Polynomial.map_map, Polynomial.map_map, he] at this
    rw [this]
    have hid : (e : R ⧸ I →+* S).comp (e.symm : S →+* R ⧸ I) = RingHom.id S := by
      ext x; simp
    rw [hid, Polynomial.map_id]
  refine ⟨g, h, hg, hh, hgh, back hgmap, back hhmap, hcopR, fun g' hg' hg'map hg'F => ?_⟩
  refine huniq g' hg' ?_ hg'F
  rw [← hg'map, Polynomial.map_map, he']

end Main

end HenselFactorisation
p2m_reactivate "P2MW.S_Polynomial_exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete.Polynomial.HenselFactorisation"

end Polynomial
p2m_reactivate "P2MW.S_Polynomial_exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete.Polynomial.HenselFactorisation P2MW.S_Polynomial_exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete.Polynomial"

theorem solution
    {R S : Type*} [CommRing R] [CommRing S] (π : R →+* S) (hπ : Function.Surjective π)
    [IsAdicComplete (RingHom.ker π) R]
    {F : Polynomial R} (hF : F.Monic) {g₀ h₀ : Polynomial S} (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hF₀ : F.map π = g₀ * h₀) :
    ∃ g h : Polynomial R, g.Monic ∧ h.Monic ∧ g * h = F ∧
      g.map π = g₀ ∧ h.map π = h₀ ∧ IsCoprime g h ∧
      ∀ g' : Polynomial R, g'.Monic → g'.map π = g₀ → g' ∣ F → g' = g :=
  Polynomial.HenselFactorisation.main_of_surjective π hπ hF hg₀ hh₀ hcop hF₀

end S_Polynomial_exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete
end P2MW
export P2MW.S_Polynomial_exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete (solution)
