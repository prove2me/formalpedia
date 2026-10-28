-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.hermitian_parity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:47:46.012795+00:00
-- url     : https://prove2.me/submissions/b6b27daa-0b79-42e6-9ba0-dcd27fecd492

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19
import Mathlib

open MvPolynomial

namespace HP_ns

/-- Hopfian: surjective ring endomorphism of a Noetherian ring is injective. -/
theorem HP_hopf {A : Type*} [CommRing A] [IsNoetherianRing A] (φ : A →+* A)
    (hs : Function.Surjective φ) : Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hmono : Monotone (fun k : ℕ => RingHom.ker (φ ^ k)) := by
    refine monotone_nat_of_le_succ (fun k y hy => ?_)
    simp only [RingHom.mem_ker, RingHom.coe_pow] at hy ⊢
    rw [Function.iterate_succ_apply', hy, map_zero]
  obtain ⟨N, hN⟩ := (monotone_stabilizes_iff_noetherian (R := A) (M := A)).mpr
    inferInstance ⟨_, hmono⟩
  have hsN : Function.Surjective (φ ^ N) := by
    rw [RingHom.coe_pow]; exact hs.iterate N
  obtain ⟨y, rfl⟩ := hsN x
  have hy : y ∈ RingHom.ker (φ ^ (N+1)) := by
    simp only [RingHom.mem_ker, RingHom.coe_pow] at hx ⊢
    rw [Function.iterate_succ_apply', hx]
  have := hN (N+1) (by omega)
  simp only [OrderHom.coe_mk] at this
  rw [← this] at hy
  exact hy

variable (n : ℕ)

noncomputable def HP_psi' : MvPolynomial (Fin n) ℝ →ₐ[ℝ] symmetricSubalgebra (Fin n) ℝ :=
  aeval (fun i : Fin n => (⟨psum (Fin n) ℝ (i+1), psum_isSymmetric _ _ _⟩ :
    symmetricSubalgebra (Fin n) ℝ))

noncomputable def HP_psi : MvPolynomial (Fin n) ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ :=
  aeval (fun i : Fin n => psum (Fin n) ℝ (i+1))

theorem HP_psi_val (p : MvPolynomial (Fin n) ℝ) : ((HP_psi' n p) : MvPolynomial (Fin n) ℝ) = HP_psi n p := by
  rw [HP_psi', HP_psi, ← Subalgebra.mvPolynomial_aeval_coe]

theorem HP_psum_mem (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ n) : psum (Fin n) ℝ k ∈ (HP_psi n).range := by
  refine (AlgHom.mem_range _).mpr ⟨X ⟨k-1, by omega⟩, ?_⟩
  rw [HP_psi, aeval_X]
  congr 1; show k - 1 + 1 = k; omega

theorem HP_esymm_mem (k : ℕ) (hk : k ≤ n) : esymm (Fin n) ℝ k ∈ (HP_psi n).range := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [esymm_zero]; exact Subalgebra.one_mem _
  have h := mul_esymm_eq_sum (Fin n) ℝ k
  have hmem : (k : MvPolynomial (Fin n) ℝ) * esymm (Fin n) ℝ k ∈ (HP_psi n).range := by
    rw [h]
    refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _) ?_
    refine Subalgebra.sum_mem _ (fun a ha => ?_)
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at ha1
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _
      (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _) (ih _ ha2 (by omega))) ?_
    exact HP_psum_mem n _ (by omega) (by omega)
  have : esymm (Fin n) ℝ k = ((k : ℝ)⁻¹) • ((k : MvPolynomial (Fin n) ℝ) * esymm (Fin n) ℝ k) := by
    · have : ((k:ℝ)⁻¹) • (k : MvPolynomial (Fin n) ℝ) = 1 := by
        rw [← map_natCast (C : ℝ →+* MvPolynomial (Fin n) ℝ), smul_eq_C_mul, ← C_mul,
          inv_mul_cancel₀ (by exact_mod_cast hk0.ne'), C_1]
      rw [← smul_mul_assoc, this, one_mul]
  rw [this]
  exact Subalgebra.smul_mem _ hmem _

theorem HP_psi_injective : Function.Injective (HP_psi n) := by
  let E := esymmAlgEquiv (Fin n) ℝ (Fintype.card_fin n)
  let φ : MvPolynomial (Fin n) ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ :=
    (E.symm : symmetricSubalgebra (Fin n) ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ).comp (HP_psi' n)
  have hgen : ∀ i : Fin n, (⟨esymm (Fin n) ℝ (i+1), esymm_isSymmetric _ _ _⟩ :
      symmetricSubalgebra (Fin n) ℝ) ∈ (HP_psi' n).range := by
    intro i
    obtain ⟨x, hx⟩ := (AlgHom.mem_range _).mp (HP_esymm_mem n (i+1) (by omega))
    refine (AlgHom.mem_range _).mpr ⟨x, Subtype.ext ?_⟩
    rw [HP_psi_val]; exact hx
  have hrange : ∀ p, esymmAlgHom (Fin n) ℝ n p ∈ (HP_psi' n).range := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r => rw [← algebraMap_eq, AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ _
    | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
    | mul_X p i hp =>
      rw [map_mul]
      refine Subalgebra.mul_mem _ hp ?_
      rw [esymmAlgHom, aeval_X]
      exact hgen i
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := (AlgHom.mem_range _).mp (hrange y)
    refine ⟨x, ?_⟩
    show E.symm (HP_psi' n x) = y
    rw [hx]
    exact E.symm_apply_apply y
  have hinj := HP_hopf (φ : MvPolynomial (Fin n) ℝ →+* MvPolynomial (Fin n) ℝ) hsurj
  intro a b hab
  apply hinj
  show E.symm (HP_psi' n a) = E.symm (HP_psi' n b)
  congr 1
  exact Subtype.ext (by rw [HP_psi_val, HP_psi_val, hab])

open QAlgorithms.Papers.Independent.Information100.P19

def HP_g (hn : 0 < n) (j : ℕ) : Fin n := ⟨j % n, Nat.mod_lt _ hn⟩

noncomputable def HP_E (hn : 0 < n) (L : List ℕ) : Fin n →₀ ℕ :=
  (L.map fun k => Finsupp.single (HP_g n hn (k-1)) 1).sum

theorem HP_prodX (hn : 0 < n) (L : List ℕ) :
    (L.map fun k => (X (HP_g n hn (k-1)) : MvPolynomial (Fin n) ℝ)).prod
      = monomial (HP_E n hn L) 1 := by
  induction L with
  | nil => simp [HP_E]
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, ih]
    simp only [HP_E, List.map_cons, List.sum_cons]
    rw [X, monomial_mul, one_mul]

theorem HP_E_apply (hn : 0 < n) (L : List ℕ) (hL : ∀ k ∈ L, 1 ≤ k ∧ k ≤ n) (i : Fin n) :
    HP_E n hn L i = L.count (i.val+1) := by
  induction L with
  | nil => simp [HP_E]
  | cons a L ih =>
    have ha := hL a (by simp)
    rw [HP_E, List.map_cons, List.sum_cons, Finsupp.add_apply, ← HP_E,
      ih (fun k hk => hL k (by simp [hk])), List.count_cons, Finsupp.single_apply]
    have : (HP_g n hn (a-1) = i) ↔ (a = i.val + 1) := by
      rw [Fin.ext_iff]
      show (a-1) % n = i.val ↔ _
      rw [Nat.mod_eq_of_lt (by omega)]
      constructor <;> intro h <;> omega
    by_cases h : a = i.val + 1
    · rw [if_pos (this.mpr h)]; simp [h]; omega
    · rw [if_neg (fun h' => h (this.mp h'))]; simp [h]

theorem HP_psi_prod (hn : 0 < n) (L : List ℕ) (hL : ∀ k ∈ L, 1 ≤ k ∧ k ≤ n) :
    HP_psi n ((L.map fun k => (X (HP_g n hn (k-1)) : MvPolynomial (Fin n) ℝ)).prod)
      = (L.map fun k => psum (Fin n) ℝ k).prod := by
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k hk
  have := hL k hk
  simp only [Function.comp_apply, HP_psi, aeval_X]
  congr 1
  show (k-1) % n + 1 = k
  rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem HP_part_bound {l : Part n} {k : ℕ} (hk : k ∈ l.val) : 1 ≤ k ∧ k ≤ n := by
  refine ⟨l.2.2.1 k hk, ?_⟩
  rw [← l.2.2.2]
  exact List.le_sum_of_mem hk

theorem HP_E_inj (hn : 0 < n) (l l' : Part n) (h : HP_E n hn l.val = HP_E n hn l'.val) :
    l = l' := by
  have hc : ∀ a, l.val.count a = l'.val.count a := by
    intro a
    by_cases ha : 1 ≤ a ∧ a ≤ n
    · have := DFunLike.congr_fun h ⟨a-1, by omega⟩
      rw [HP_E_apply n hn _ (fun k hk => HP_part_bound n hk),
        HP_E_apply n hn _ (fun k hk => HP_part_bound n hk)] at this
      have e : a - 1 + 1 = a := by omega
      simpa [e] using this
    · rw [List.count_eq_zero.mpr (fun hm => ha (HP_part_bound n hm)),
        List.count_eq_zero.mpr (fun hm => ha (HP_part_bound n hm))]
  apply Subtype.ext
  exact List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h2 h1) l.2.1 l'.2.1
    (List.perm_iff_count.mpr hc)

theorem HP_indep (hn : 0 < n) (f : Coeff n)
    (h : ∀ x : Fin n → ℝ, pairing f (spectralMoments x) = 0) : f = 0 := by
  classical
  let Q : MvPolynomial (Fin n) ℝ := f.sum fun l c => monomial (HP_E n hn l.val) c
  have hQ : ∀ x, eval x (HP_psi n Q) = pairing f (spectralMoments x) := by
    intro x
    simp only [Q, pairing, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show monomial (HP_E n hn l.val) (f l) = C (f l) * monomial (HP_E n hn l.val) 1 by
        rw [C_mul_monomial, mul_one], ← HP_prodX, map_mul,
      HP_psi_prod n hn _ (fun k hk => HP_part_bound n hk),
      show HP_psi n (C (f l)) = C (f l) from (HP_psi n).commutes _, map_mul,
      eval_C, map_list_prod, List.map_map, spectralMoments]
    congr 2
    apply List.map_congr_left
    intro k _
    simp [psum]
  have hQ0 : Q = 0 := by
    apply HP_psi_injective n
    rw [map_zero]
    apply MvPolynomial.funext
    intro x
    rw [hQ, h, map_zero]
  ext l
  have := congrArg (coeff (HP_E n hn l.val)) hQ0
  simp only [Q, Finsupp.sum, coeff_sum, coeff_monomial, coeff_zero] at this
  rw [Finset.sum_eq_single l] at this
  · simpa using this
  · intro b _ hb
    rw [if_neg]
    exact fun e => hb (HP_E_inj n hn _ _ e)
  · intro hl
    rw [Finsupp.notMem_support_iff.mp hl]; simp

theorem HP_neg_prod (L : List ℕ) (g : ℕ → ℝ) :
    (L.map fun k => (-1:ℝ)^k * g k).prod = (-1)^L.sum * (L.map g).prod := by
  induction L with
  | nil => simp
  | cons a L ih => rw [List.map_cons, List.prod_cons, ih, List.sum_cons, List.map_cons,
      List.prod_cons, pow_add]; ring

theorem HP_pairing_single {m : ℕ} (l : Part m) (y : Part m → ℝ) :
    pairing (Finsupp.single l 1) y = y l := by
  rw [pairing, Finsupp.sum_single_index (by simp), one_mul]

theorem HP_even_mem {m : ℕ} (l : Part m) (h : ∀ k ∈ l.val, Even k) :
    Finsupp.single l 1 ∈ allCone m := by
  intro d _ x
  rw [HP_pairing_single, spectralMoments]
  apply List.prod_nonneg
  intro a ha
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
  exact Finset.sum_nonneg (fun i _ => (h k hk).pow_nonneg _)

theorem HP_odd (n : ℕ) (hn : 1 ≤ n) (ho : Odd n) : allCone n = {0} := by
  ext f
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hf
    apply HP_indep n (by omega) f
    intro x
    have h1 := hf n (by omega) x
    have h2 := hf n (by omega) (-x)
    have hneg : spectralMoments (n := n) (-x) = fun l => - spectralMoments x l := by
      funext l
      rw [spectralMoments, spectralMoments]
      have : (fun k => ∑ i, (-x) i ^ k) = fun k => (-1:ℝ)^k * ∑ i, x i ^ k := by
        funext k; rw [Finset.mul_sum]; congr 1; funext i
        rw [Pi.neg_apply, neg_pow]
      rw [this, HP_neg_prod, l.2.2.2, ho.neg_one_pow, neg_one_mul]
    have : pairing f (spectralMoments (n := n) (-x)) = - pairing f (spectralMoments x) := by
      rw [hneg, pairing, pairing, Finsupp.sum, Finsupp.sum, ← Finset.sum_neg_distrib]
      simp only [mul_neg]
    linarith
  · rintro rfl d _ x
    simp [pairing]

end HP_ns

namespace QAlgorithms.Papers.Independent.Information100.P19

end QAlgorithms.Papers.Independent.Information100.P19

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (Odd n → allCone n = {0}) ∧
    (Even n → ∀ l : QAlgorithms.Papers.Independent.Information100.P19.Part n, (∀ k ∈ l.val, Even k) → Finsupp.single l 1 ∈ allCone n) ∧
    (∀ m : ℕ, 1 ≤ m → ∀ l : QAlgorithms.Papers.Independent.Information100.P19.Part (2*m), l.val = [2*m] →
      Finsupp.single l 1 ∈ allCone (2*m)) := by
  refine ⟨HP_ns.HP_odd n hn, fun _ l hl => HP_ns.HP_even_mem l hl, ?_⟩
  intro m _ l hl
  apply HP_ns.HP_even_mem l
  intro k hk
  rw [hl, List.mem_singleton] at hk
  rw [hk]; exact even_two_mul m

