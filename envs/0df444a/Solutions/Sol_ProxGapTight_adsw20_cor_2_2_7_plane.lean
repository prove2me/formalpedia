-- Prove2me | solution 1 for ProxGapTight.adsw20_cor_2_2_7_plane
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T00:50:22.05506+00:00
-- url     : https://prove2.me/submissions/ea030442-6300-4037-bb21-c786769caa17

import Mathlib
import Definitions.Def_ProxGapTight_Lines

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL
open ProxGapTight Polynomial
/-!
q366 planar blueprint: a proof of `ProxGapTight.adsw20_cor_2_2_7_plane`. Mathematics:
p2m-standalone/missions/q366-stoc-johnson-proximity-gaps-retry/notes/PLANAR_PLAN.md.
Development only.
-/
/-- lines of the plane `PG(2, K)`: 2-dimensional subspaces of `K^3` -/
abbrev Ln (K : Type) [Field K] : Type :=
  {H : Submodule K (Fin 3 → K) // Module.finrank K H + 1 = 3}

/-- incidence vector of a line of the plane -/
noncomputable def ind1 {K : Type} [Field K] (p : ℕ) (H : Ln K) : Lines K 3 → ZMod p :=
  Set.indicator {ℓ : Lines K 3 | ℓ.1 ≤ H.1} (fun _ => (1 : ZMod p))

/-- the code `C_1(2, q)` -/
noncomputable def C1 (K : Type) [Field K] (p : ℕ) : Submodule (ZMod p) (Lines K 3 → ZMod p) :=
  Submodule.span (ZMod p) (Set.range fun H : Ln K => ind1 p H)

/-- number of support points on a line -/
noncomputable def sm {K : Type} [Field K] [Fintype K] {p : ℕ} (v : Lines K 3 → ZMod p)
    (H : Ln K) : ℕ := by
  classical exact (Finset.univ.filter fun ℓ : Lines K 3 => ℓ.1 ≤ H.1 ∧ v ℓ ≠ 0).card

/-- number of points of a line where `v` takes the value `r` -/
noncomputable def cnt {K : Type} [Field K] [Fintype K] {p : ℕ} (v : Lines K 3 → ZMod p)
    (H : Ln K) (r : ZMod p) : ℕ := by
  classical exact (Finset.univ.filter fun ℓ : Lines K 3 => ℓ.1 ≤ H.1 ∧ v ℓ = r).card

/-- Bagchi's type (the second alternative of item 2 of the plane statement) -/
def OddType {K : Type} [Field K] {p : ℕ} (v : Lines K 3 → ZMod p) : Prop :=
  ∃ S : Lines K 3, ∃ H₁ H₂ H₃ : Ln K,
    S.1 ≤ H₁.1 ∧ S.1 ≤ H₂.1 ∧ S.1 ≤ H₃.1 ∧ H₁ ≠ H₂ ∧ H₁ ≠ H₃ ∧ H₂ ≠ H₃ ∧
    (∀ ℓ : Lines K 3, v ℓ ≠ 0 → ℓ.1 ≤ H₁.1 ∨ ℓ.1 ≤ H₂.1 ∨ ℓ.1 ≤ H₃.1) ∧
    ∀ H ∈ ({H₁, H₂, H₃} : Set (Ln K)),
      ∀ ℓ ℓ' : Lines K 3, ℓ.1 ≤ H.1 → ℓ'.1 ≤ H.1 → ℓ ≠ S → ℓ' ≠ S → v ℓ = v ℓ' → ℓ = ℓ'

/-- at most three lines -/
def Three {K : Type} [Field K] (p : ℕ) (v : Lines K 3 → ZMod p) : Prop :=
  ∃ H₁ H₂ H₃ : Ln K, ∃ α β γ : ZMod p, v = α • ind1 p H₁ + β • ind1 p H₂ + γ • ind1 p H₃

end ProxGapTight.Dev.Q366PL
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL.PartR
open ProxGapTight ProxGapTight.Dev.Q366PL Polynomial
/-! ### The subresultant matrix

Columns `k < a` stand for the monomials `X^k` of `A`, columns `k ≥ a` for the monomials
`X^(k-a)` of `B`; row `e` is the coefficient of `X^(j+e)` of `A * u + B * v`. -/
/-- the subresultant matrix -/
noncomputable def Mat {R : Type} [CommRing R] (u v : R[X]) (j a N : ℕ) :
    Matrix (Fin N) (Fin N) R :=
  fun e k => if (k : ℕ) < a then (X ^ (k : ℕ) * u).coeff (j + e)
    else (X ^ ((k : ℕ) - a) * v).coeff (j + e)

/-- the `A`-part of a coefficient vector -/
noncomputable def Apoly {R : Type} [CommRing R] {N : ℕ} (a : ℕ) (z : Fin N → R) : R[X] :=
  ∑ k : Fin N, if (k : ℕ) < a then C (z k) * X ^ (k : ℕ) else 0

/-- the `B`-part of a coefficient vector -/
noncomputable def Bpoly {R : Type} [CommRing R] {N : ℕ} (a : ℕ) (z : Fin N → R) : R[X] :=
  ∑ k : Fin N, if (k : ℕ) < a then 0 else C (z k) * X ^ ((k : ℕ) - a)

/-- the coefficient vector of a pair `(A, B)` -/
noncomputable def vec {R : Type} [CommRing R] (N a : ℕ) (A B : R[X]) : Fin N → R :=
  fun k => if (k : ℕ) < a then A.coeff k else B.coeff ((k : ℕ) - a)

lemma Mat_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (u v : R[X]) (j a N : ℕ) :
    (Mat u v j a N).map f = Mat (u.map f) (v.map f) j a N := by
  ext e k
  simp only [Matrix.map_apply, Mat]
  split_ifs <;> rw [coeff_X_pow_mul', coeff_X_pow_mul'] <;> split_ifs <;> simp

lemma Mat_mulVec {R : Type} [CommRing R] (u v : R[X]) (j a N : ℕ) (z : Fin N → R)
    (e : Fin N) :
    (Mat u v j a N).mulVec z e = (Apoly a z * u + Bpoly a z * v).coeff (j + e) := by
  simp only [Matrix.mulVec, dotProduct, Apoly, Bpoly, Finset.sum_mul, coeff_add,
    finsetSum_coeff, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Mat]
  split_ifs <;> simp only [zero_mul, coeff_zero, add_zero, zero_add, mul_assoc, coeff_C_mul] <;>
    ring

lemma Apoly_coeff {R : Type} [CommRing R] {N : ℕ} (a : ℕ) (z : Fin N → R) (i : ℕ) :
    (Apoly a z).coeff i = if h : i < a ∧ i < N then z ⟨i, h.2⟩ else 0 := by
  simp only [Apoly, finsetSum_coeff]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i, h.2⟩]
    · simp [h.1]
    · intro k _ hk
      have hki : (k : ℕ) ≠ i := fun h' => hk (Fin.ext h')
      split_ifs <;> simp [Ne.symm hki]
    · simp
  · refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs with hk
    · rw [coeff_C_mul_X_pow, if_neg]
      intro hik
      exact h ⟨hik ▸ hk, hik ▸ k.2⟩
    · simp

lemma Bpoly_coeff {R : Type} [CommRing R] {N : ℕ} (a : ℕ) (z : Fin N → R) (i : ℕ) :
    (Bpoly a z).coeff i = if h : a + i < N then z ⟨a + i, h⟩ else 0 := by
  simp only [Bpoly, finsetSum_coeff]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a + i, h⟩]
    · simp
    · intro k _ hk
      have hki : (k : ℕ) ≠ a + i := fun h' => hk (Fin.ext h')
      split_ifs with hka
      · simp
      · rw [coeff_C_mul_X_pow, if_neg]
        omega
    · simp
  · refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs with hk
    · simp
    · rw [coeff_C_mul_X_pow, if_neg]
      intro hik
      exact h (by omega)

lemma Apoly_degree {R : Type} [CommRing R] {N : ℕ} (a : ℕ) (z : Fin N → R) :
    (Apoly a z).degree < a := by
  rw [← mem_degreeLT]
  refine Submodule.sum_mem _ fun k _ => ?_
  split_ifs with hk
  · rw [mem_degreeLT]
    exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast hk)
  · exact Submodule.zero_mem _

lemma Bpoly_degree {R : Type} [CommRing R] {N : ℕ} (a : ℕ) (z : Fin N → R) :
    (Bpoly a z).degree < (N - a : ℕ) := by
  rw [← mem_degreeLT]
  refine Submodule.sum_mem _ fun k _ => ?_
  split_ifs with hk
  · exact Submodule.zero_mem _
  · rw [mem_degreeLT]
    exact (degree_C_mul_X_pow_le _ _).trans_lt (by have := k.2; exact_mod_cast (by omega))

lemma Apoly_vec {R : Type} [CommRing R] (N a : ℕ) (haN : a ≤ N) (A B : R[X])
    (hA : A.degree < a) : Apoly a (vec N a A B) = A := by
  ext i
  rw [Apoly_coeff]
  split_ifs with h
  · simp [vec, h.1]
  · symm
    apply coeff_eq_zero_of_degree_lt
    refine hA.trans_le ?_
    exact_mod_cast (by omega : a ≤ i)

lemma Bpoly_vec {R : Type} [CommRing R] (N a : ℕ) (A B : R[X])
    (hB : B.degree < (N - a : ℕ)) : Bpoly a (vec N a A B) = B := by
  ext i
  rw [Bpoly_coeff]
  split_ifs with h
  · simp [vec]
  · symm
    apply coeff_eq_zero_of_degree_lt
    refine hB.trans_le ?_
    exact_mod_cast (by omega : N - a ≤ i)

/-! ### (a) the degree of the determinant -/
lemma natDegree_det_le {K : Type} [Field K] {N : ℕ} (M : Matrix (Fin N) (Fin N) K[X])
    (r c : Fin N → ℕ) (h : ∀ e k, M e k ≠ 0 → (M e k).natDegree + r e ≤ c k) :
    M.det.natDegree ≤ ∑ k, c k - ∑ e, r e := by
  rw [Matrix.det_apply']
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  by_cases hp : ∏ i, M (σ i) i = 0
  · simp [hp]
  · have hne : ∀ i, M (σ i) i ≠ 0 := fun i =>
      (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ _)
    have h1 : (∏ i, M (σ i) i).natDegree ≤ ∑ i, (M (σ i) i).natDegree :=
      natDegree_prod_le _ _
    have h2 : ∑ i, ((M (σ i) i).natDegree + r (σ i)) ≤ ∑ i, c i :=
      Finset.sum_le_sum fun i _ => h _ _ (hne i)
    have h3 : ∑ i, r (σ i) = ∑ e, r e := Equiv.sum_comp σ r
    rw [Finset.sum_add_distrib, h3] at h2
    have h4 : ((((Equiv.Perm.sign σ : ℤ) : K[X])) * ∏ i, M (σ i) i).natDegree ≤
        (∏ i, M (σ i) i).natDegree := by
      refine natDegree_mul_le.trans ?_
      simp
    omega

lemma sum_wt (j a s : ℕ) :
    ∑ k : Fin (a + s), (if (k : ℕ) < a then j + s + k else j + a + ((k : ℕ) - a)) =
      ∑ e : Fin (a + s), (j + (e : ℕ)) + a * s := by
  rw [Fin.sum_univ_eq_sum_range (fun t => if t < a then j + s + t else j + a + (t - a)),
    Fin.sum_univ_eq_sum_range (fun t => j + t), Finset.sum_range_add, Finset.sum_range_add]
  have e1 : ∑ x ∈ Finset.range a, (if x < a then j + s + x else j + a + (x - a)) =
      ∑ x ∈ Finset.range a, (j + s + x) :=
    Finset.sum_congr rfl fun x hx => by rw [if_pos (Finset.mem_range.mp hx)]
  have e2 : ∑ x ∈ Finset.range s, (if a + x < a then j + s + (a + x) else j + a + (a + x - a)) =
      ∑ x ∈ Finset.range s, (j + a + x) :=
    Finset.sum_congr rfl fun x _ => by rw [if_neg (by omega)]; omega
  have e3 : ∑ x ∈ Finset.range s, (j + (a + x)) = ∑ x ∈ Finset.range s, (j + a + x) :=
    Finset.sum_congr rfl fun x _ => by omega
  rw [e1, e2, e3]
  have e4 : ∑ x ∈ Finset.range a, (j + s + x) = ∑ x ∈ Finset.range a, (j + x) + a * s := by
    rw [Finset.sum_congr rfl (fun x _ => (by ring : j + s + x = (j + x) + s)),
      Finset.sum_add_distrib]
    simp
  omega

/-! ### (c) a kernel of dimension `h` forces `(X - y)^h ∣ det` -/
lemma pow_dvd_det {K : Type} [Field K] {N : ℕ} (y : K) :
    ∀ (h : ℕ) (M : Matrix (Fin N) (Fin N) K[X]),
      h ≤ Module.finrank K (LinearMap.ker (M.map (evalRingHom y)).mulVecLin) →
      (X - C y) ^ h ∣ M.det := by
  intro h
  induction h with
  | zero => intro M _; simp
  | succ h ih =>
    intro M hM
    have hpos : 0 < Module.finrank K (LinearMap.ker (M.map (evalRingHom y)).mulVecLin) := by
      omega
    have hne : LinearMap.ker (M.map (evalRingHom y)).mulVecLin ≠ ⊥ := by
      intro hb
      rw [hb, finrank_bot] at hpos
      exact lt_irrefl _ hpos
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨c, hc⟩ : ∃ c, w c ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hw0 (funext hcon)
    have hker : (M.map (evalRingHom y)).mulVec w = 0 := LinearMap.mem_ker.mp hwW
    have hroot : ∀ i, (X - C y) ∣ M.mulVec (fun k => C (w k)) i := by
      intro i
      rw [dvd_iff_isRoot, IsRoot.def, ← coe_evalRingHom, RingHom.map_mulVec]
      have hw : (evalRingHom y) ∘ (fun k => C (w k)) = w := by
        funext k
        simp
      rw [hw, hker]
      rfl
    choose g hg using hroot
    have hdet : M.det * C (w c) = (X - C y) * (M.updateCol c g).det := by
      have h1 : (M.updateCol c (M.mulVec (fun k => C (w k)))).det = M.det * C (w c) := by
        rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec,
          Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
        simp
      rw [← h1]
      have h2 : M.mulVec (fun k => C (w k)) = (X - C y) • g := by
        funext i
        simp [hg i]
      rw [h2, Matrix.det_updateCol_smul]
    have hM' : h ≤ Module.finrank K
        (LinearMap.ker ((M.updateCol c g).map (evalRingHom y)).mulVecLin) := by
      set W := LinearMap.ker (M.map (evalRingHom y)).mulVecLin
      have hsub : W ⊓ LinearMap.ker (LinearMap.proj c : (Fin N → K) →ₗ[K] K) ≤ LinearMap.ker ((M.updateCol c g).map (evalRingHom y)).mulVecLin := by
        rintro z ⟨hzW, hzP⟩
        have hz : (M.map (evalRingHom y)).mulVec z = 0 := LinearMap.mem_ker.mp hzW
        have hzc : z c = 0 := hzP
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        funext i
        rw [← congrFun hz i]
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : k = c
        · rw [hk, hzc]
          simp
        · rw [Matrix.updateCol_apply, if_neg hk]
      have hP : Module.finrank K (LinearMap.ker (LinearMap.proj c : (Fin N → K) →ₗ[K] K)) + 1 ≥ N := by
        have := LinearMap.finrank_range_add_finrank_ker
          (LinearMap.proj c : (Fin N → K) →ₗ[K] K)
        have hr := Submodule.finrank_le (LinearMap.range
          (LinearMap.proj c : (Fin N → K) →ₗ[K] K))
        rw [Module.finrank_self] at hr
        rw [Module.finrank_fin_fun] at this
        omega
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq W
        (LinearMap.ker (LinearMap.proj c : (Fin N → K) →ₗ[K] K))
      have hle := Submodule.finrank_le (W ⊔
        LinearMap.ker (LinearMap.proj c : (Fin N → K) →ₗ[K] K))
      rw [Module.finrank_fin_fun] at hle
      have hmono := Submodule.finrank_mono hsub
      omega
    have h3 := ih _ hM'
    have h4 : (X - C y) ^ (h + 1) ∣ M.det * C (w c) := by
      rw [hdet, pow_succ']
      exact mul_dvd_mul_left _ h3
    exact (IsUnit.dvd_mul_right (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc))).mp h4

/-! ### (b) at `y0` the kernel is trivial -/
lemma ker_trivial {K : Type} [Field K] [DecidableEq K] (u v : K[X]) (n m s j a : ℕ)
    (hm : 1 ≤ m) (hu0 : u ≠ 0) (hun : u.natDegree = n) (hv : v.natDegree ≤ n - m)
    (hjs : j + s = n) (ham : a + m = s)
    (hg : (gcd u v).natDegree = j) (z : Fin (a + s) → K)
    (hz : (Mat u v j a (a + s)).mulVec z = 0) : z = 0 := by
  have hA : (Apoly a z).degree < a := Apoly_degree a z
  have hB : (Bpoly a z).degree < (a + s - a : ℕ) := Bpoly_degree a z
  have hcoef : ∀ t, j ≤ t → (Apoly a z * u + Bpoly a z * v).coeff t = 0 := by
    intro t ht
    by_cases htN : t < j + (a + s)
    · have h1 := congrFun hz ⟨t - j, by omega⟩
      rw [Mat_mulVec] at h1
      have h2 : j + ((⟨t - j, by omega⟩ : Fin (a + s)) : ℕ) = t := by simp; omega
      rw [h2] at h1
      exact h1
    · apply coeff_eq_zero_of_natDegree_lt
      refine (natDegree_add_le _ _).trans_lt (max_lt ?_ ?_)
      · by_cases hA0 : Apoly a z = 0
        · rw [hA0, zero_mul, natDegree_zero]; omega
        have := (natDegree_lt_iff_degree_lt hA0).mpr hA
        exact natDegree_mul_le.trans_lt (by omega)
      · by_cases hB0 : Bpoly a z = 0
        · rw [hB0, zero_mul, natDegree_zero]; omega
        have := (natDegree_lt_iff_degree_lt hB0).mpr hB
        exact natDegree_mul_le.trans_lt (by omega)
  have hP : Apoly a z * u + Bpoly a z * v = 0 := by
    by_contra hP
    have hd : gcd u v ∣ Apoly a z * u + Bpoly a z * v :=
      dvd_add (dvd_mul_of_dvd_right (gcd_dvd_left u v) _)
        (dvd_mul_of_dvd_right (gcd_dvd_right u v) _)
    have hlt : (Apoly a z * u + Bpoly a z * v).natDegree < j := by
      by_contra hge
      push Not at hge
      exact hP (leadingCoeff_eq_zero.mp (hcoef _ hge))
    have := natDegree_le_of_dvd hd hP
    omega
  have hg0 : gcd u v ≠ 0 := fun h => hu0 ((gcd_eq_zero_iff u v).mp h).1
  have hB0 : Bpoly a z = 0 := by
    by_contra hB0
    have h1 : u ∣ Bpoly a z * v := ⟨-Apoly a z, by linear_combination hP⟩
    have h2 : u ∣ Bpoly a z * u := dvd_mul_left u _
    have h3 : u ∣ gcd (Bpoly a z * v) (Bpoly a z * u) := dvd_gcd h1 h2
    rw [gcd_mul_left, gcd_comm v u] at h3
    have h4 : u ∣ Bpoly a z * gcd u v :=
      h3.trans (mul_dvd_mul_right (normalize_associated _).dvd _)
    have h5 := natDegree_le_of_dvd h4 (mul_ne_zero hB0 hg0)
    rw [natDegree_mul hB0 hg0] at h5
    have := (natDegree_lt_iff_degree_lt hB0).mpr hB
    omega
  have hA0 : Apoly a z = 0 := by
    rw [hB0, zero_mul, add_zero] at hP
    exact (mul_eq_zero.mp hP).resolve_right hu0
  funext k
  by_cases hk : (k : ℕ) < a
  · have h1 := Apoly_coeff a z k
    rw [hA0, coeff_zero, dif_pos ⟨hk, k.2⟩] at h1
    exact h1.symm
  · have h1 := Bpoly_coeff a z ((k : ℕ) - a)
    rw [hB0, coeff_zero, dif_pos (by omega)] at h1
    have hk' : (⟨a + ((k : ℕ) - a), by omega⟩ : Fin (a + s)) = k := Fin.ext (by simp; omega)
    rw [hk'] at h1
    exact h1.symm

/-! ### (c) a gcd of degree `j + h` gives a kernel of dimension `h` -/
lemma ker_large {K : Type} [Field K] [DecidableEq K] (u v : K[X]) (n m s j a h : ℕ)
    (hu0 : u ≠ 0) (hun : u.natDegree = n) (hv : v.natDegree ≤ n - m)
    (hjs : j + s = n) (ham : a + m = s)
    (hg : (gcd u v).natDegree = j + h) :
    h ≤ Module.finrank K (LinearMap.ker (Mat u v j a (a + s)).mulVecLin) := by
  set g := gcd u v with hgdef
  obtain ⟨u', hu'⟩ : g ∣ u := gcd_dvd_left u v
  obtain ⟨v', hv'⟩ : g ∣ v := gcd_dvd_right u v
  have hg0 : g ≠ 0 := fun h => hu0 ((gcd_eq_zero_iff u v).mp h).1
  have hu'0 : u' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hu'
    exact hu0 hu'
  have hdu' : u'.natDegree + (j + h) = n := by
    rw [← hun, hu', natDegree_mul hg0 hu'0]
    omega
  have hdv' : v' ≠ 0 → v'.natDegree + (j + h) ≤ n - m := by
    intro hv'0
    rw [hv', natDegree_mul hg0 hv'0] at hv
    omega
  have hAdeg : ∀ p : K[X], p.degree < h → (v' * p).degree < a := by
    intro p hp
    by_cases h0 : v' * p = 0
    · rw [h0, degree_zero]
      exact WithBot.bot_lt_coe a
    have hv'0 : v' ≠ 0 := left_ne_zero_of_mul h0
    have hp0 : p ≠ 0 := right_ne_zero_of_mul h0
    rw [← natDegree_lt_iff_degree_lt h0, natDegree_mul hv'0 hp0]
    have := (natDegree_lt_iff_degree_lt hp0).mpr hp
    have := hdv' hv'0
    omega
  have hBdeg : ∀ p : K[X], p.degree < h → (-(u' * p)).degree < (a + s - a : ℕ) := by
    intro p hp
    rw [degree_neg]
    by_cases hp0 : p = 0
    · rw [hp0, mul_zero, degree_zero]
      exact WithBot.bot_lt_coe _
    have h0 : u' * p ≠ 0 := mul_ne_zero hu'0 hp0
    rw [← natDegree_lt_iff_degree_lt h0, natDegree_mul hu'0 hp0]
    have := (natDegree_lt_iff_degree_lt hp0).mpr hp
    omega
  let L : K[X]_h →ₗ[K] (Fin (a + s) → K) :=
    { toFun := fun p => vec (a + s) a (v' * p.1) (-(u' * p.1))
      map_add' := by
        intro p q
        funext k
        simp only [vec, Submodule.coe_add, mul_add, neg_add, coeff_add, Pi.add_apply]
        split_ifs <;> rfl
      map_smul' := by
        intro c p
        funext k
        simp only [vec, Submodule.coe_smul, mul_smul_comm, coeff_smul, smul_eq_mul,
          Pi.smul_apply, RingHom.id_apply, ← smul_neg]
        split_ifs <;> rfl }
  have hLB : ∀ p : K[X]_h, Bpoly a (L p) = -(u' * p.1) := fun p =>
    Bpoly_vec (a + s) a _ _ (hBdeg p.1 (mem_degreeLT.mp p.2))
  have hmem : ∀ p : K[X]_h, L p ∈ LinearMap.ker (Mat u v j a (a + s)).mulVecLin := by
    intro p
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext e
    rw [Mat_mulVec, hLB, Pi.zero_apply]
    have hA : Apoly a (L p) = v' * p.1 :=
      Apoly_vec (a + s) a (by omega) _ _ (hAdeg p.1 (mem_degreeLT.mp p.2))
    rw [hA]
    have h0 : v' * p.1 * u + -(u' * p.1) * v = 0 := by
      linear_combination (v' * p.1) * hu' - (u' * p.1) * hv'
    rw [h0, coeff_zero]
  have hinj : Function.Injective (L.codRestrict _ hmem) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    have h1 : L p = 0 := congrArg Subtype.val hp
    have h2 := hLB p
    rw [h1] at h2
    have h3 : Bpoly a (0 : Fin (a + s) → K) = 0 := by simp [Bpoly]
    rw [h3, eq_comm, neg_eq_zero] at h2
    exact Subtype.ext ((mul_eq_zero.mp h2).resolve_left hu'0)
  have hfin : Module.finrank K (K[X]_h) = h := by
    rw [(degreeLTEquiv K h).finrank_eq, Module.finrank_fin_fun]
  rw [← hfin]
  exact LinearMap.finrank_le_finrank_of_injective hinj

/-! ### (d) assembly -/
theorem R_lemma {K : Type} [Field K] [Fintype K] [DecidableEq K] (u v : K[X][X]) (n m s : ℕ)
    (hm : 1 ≤ m) (hms : m ≤ s) (hsn : s ≤ n) (hu : u.Monic) (hun : u.natDegree = n)
    (hudeg : ∀ i ≤ n, (u.coeff (n - i)).natDegree ≤ i)
    (hv : v.natDegree ≤ n - m) (hvdeg : ∀ i ≤ n - m, (v.coeff (n - m - i)).natDegree ≤ i)
    (y0 : K)
    (hy0 : (gcd (u.map (evalRingHom y0)) (v.map (evalRingHom y0))).natDegree = n - s) :
    ∑ y : K, ((gcd (u.map (evalRingHom y)) (v.map (evalRingHom y))).natDegree - (n - s)) ≤
      s * (s - m) := by
  obtain ⟨j, hjs⟩ : ∃ j, j + s = n := ⟨n - s, by omega⟩
  obtain ⟨a, ham⟩ : ∃ a, a + m = s := ⟨s - m, by omega⟩
  have e1 : n - s = j := by omega
  have e2 : s - m = a := by omega
  rw [e1, e2]
  rw [e1] at hy0
  have hspec : ∀ y : K, (Mat u v j a (a + s)).map (evalRingHom y) =
      Mat (u.map (evalRingHom y)) (v.map (evalRingHom y)) j a (a + s) := fun y =>
    Mat_map _ _ _ _ _ _
  have hu0y : ∀ y : K, u.map (evalRingHom y) ≠ 0 := fun y => (hu.map _).ne_zero
  have huny : ∀ y : K, (u.map (evalRingHom y)).natDegree = n := fun y => by
    rw [hu.natDegree_map, hun]
  have hvy : ∀ y : K, (v.map (evalRingHom y)).natDegree ≤ n - m := fun y =>
    natDegree_map_le.trans hv
  -- (b) the determinant is nonzero
  have hdet0 : (Mat u v j a (a + s)).det ≠ 0 := by
    intro h0
    have h1 : ((Mat u v j a (a + s)).map (evalRingHom y0)).det = 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    rw [hspec] at h1
    obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h1
    exact hz0 (ker_trivial _ _ n m s j a hm (hu0y y0) (huny y0) (hvy y0) hjs ham hy0 z hz)
  -- (a) the degree bound
  have hdeg : (Mat u v j a (a + s)).det.natDegree ≤ s * (s - m) := by
    have h1 := natDegree_det_le (Mat u v j a (a + s)) (fun e => j + (e : ℕ))
      (fun k => if (k : ℕ) < a then j + s + k else j + a + ((k : ℕ) - a)) (by
        intro e k hne
        simp only [Mat] at hne ⊢
        split_ifs with hk
        · rw [if_pos hk, coeff_X_pow_mul'] at hne
          rw [coeff_X_pow_mul']
          split_ifs with hle
          · rw [if_pos hle] at hne
            have hi : j + e - k ≤ n := hun ▸ le_natDegree_of_ne_zero hne
            have := hudeg (n - (j + e - k)) (Nat.sub_le _ _)
            rw [Nat.sub_sub_self hi] at this
            omega
          · rw [if_neg hle] at hne
            exact absurd rfl hne
        · rw [if_neg hk, coeff_X_pow_mul'] at hne
          rw [coeff_X_pow_mul']
          split_ifs with hle
          · rw [if_pos hle] at hne
            have hi : j + e - (k - a) ≤ n - m :=
              (le_natDegree_of_ne_zero hne).trans hv
            have := hvdeg (n - m - (j + e - (k - a))) (Nat.sub_le _ _)
            rw [Nat.sub_sub_self hi] at this
            omega
          · rw [if_neg hle] at hne
            exact absurd rfl hne)
    rw [sum_wt] at h1
    have e3 : s - m = a := by omega
    rw [e3, Nat.mul_comm s a]
    omega
  -- (c) divisibility for every `y`
  have hdvd : ∀ y : K, (X - C y) ^
      ((gcd (u.map (evalRingHom y)) (v.map (evalRingHom y))).natDegree - j) ∣
        (Mat u v j a (a + s)).det := by
    intro y
    by_cases hle : (gcd (u.map (evalRingHom y)) (v.map (evalRingHom y))).natDegree ≤ j
    · rw [Nat.sub_eq_zero_of_le hle, pow_zero]
      exact one_dvd _
    · apply pow_dvd_det y
      rw [hspec]
      exact ker_large _ _ n m s j a _ (hu0y y) (huny y) (hvy y) hjs ham (by omega)
  -- (d) the factors are coprime
  have hprod : ∏ y : K, (X - C y) ^
      ((gcd (u.map (evalRingHom y)) (v.map (evalRingHom y))).natDegree - j) ∣
        (Mat u v j a (a + s)).det := by
    refine Finset.prod_dvd_of_coprime ?_ fun y _ => hdvd y
    intro x _ y _ hxy
    exact IsCoprime.pow (pairwise_coprime_X_sub_C (s := id) Function.injective_id hxy)
  have h1 := natDegree_le_of_dvd hprod hdet0
  rw [natDegree_prod _ _ (fun y _ => pow_ne_zero _ (X_sub_C_ne_zero y))] at h1
  simp only [natDegree_pow, natDegree_X_sub_C, mul_one] at h1
  have e3 : s * (s - m) = s * a := by rw [e2]
  omega

end ProxGapTight.Dev.Q366PL.PartR
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL
open ProxGapTight Polynomial
/-! ## Part R: the Szőnyi–Weiner resultant lemma (pure algebra) -/
alias R_lemma := ProxGapTight.Dev.Q366PL.PartR.R_lemma

end ProxGapTight.Dev.Q366PL
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL.PartF
open ProxGapTight ProxGapTight.Dev.Q366PL Polynomial
variable {K : Type} [Field K]
/-!
q366 planar blueprint, Part F: `F1_lemma` (a line is full or `s(q+1-s) ≤ w`), via the
Szőnyi–Weiner resultant lemma `R_lemma` (PLANAR_PLAN.md §F1).
-/
/-! ## Geometry: coordinates on the plane -/
theorem line_gen (ℓ : Lines K 3) : ∃ r : Fin 3 → K, r ≠ 0 ∧ ℓ.1 = K ∙ r := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp ℓ.2
  refine ⟨v.1, fun h => hv0 (Subtype.ext h), le_antisymm (fun y hy => ?_)
    ((Submodule.span_singleton_le_iff_mem _ _).mpr v.2)⟩
  obtain ⟨c, hc⟩ := hv ⟨y, hy⟩
  have : c • v.1 = y := congrArg Subtype.val hc
  rw [← this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem line_eq_of_le {ℓ ℓ' : Lines K 3} (h : ℓ.1 ≤ ℓ'.1) : ℓ = ℓ' :=
  Subtype.ext (Submodule.eq_of_le_of_finrank_eq h (by rw [ℓ.2, ℓ'.2]))

/-- three independent vectors -/
def Indep (e1 e2 e3 : Fin 3 → K) : Prop :=
  ∀ a b c : K, a • e1 + b • e2 + c • e3 = 0 → a = 0 ∧ b = 0 ∧ c = 0

/-- the vector of the affine point `(y, t)` -/
def vec (e1 e2 e3 : Fin 3 → K) (y t : K) : Fin 3 → K := e3 + y • e1 + t • e2

theorem vec_ne {e1 e2 e3 : Fin 3 → K} (hI : Indep e1 e2 e3) (y t : K) : vec e1 e2 e3 y t ≠ 0 := by
  intro h
  have := (hI y t 1 (by rw [← h]; unfold vec; module)).2.2
  exact one_ne_zero this

/-- the affine point `(y, t)` -/
def pt {e1 e2 e3 : Fin 3 → K} (hI : Indep e1 e2 e3) (y t : K) : Lines K 3 :=
  ⟨K ∙ vec e1 e2 e3 y t, finrank_span_singleton (vec_ne hI y t)⟩

theorem pt_le_iff {e1 e2 e3 : Fin 3 → K} (hI : Indep e1 e2 e3) (y t : K)
    (L : Submodule K (Fin 3 → K)) : (pt hI y t).1 ≤ L ↔ vec e1 e2 e3 y t ∈ L :=
  Submodule.span_singleton_le_iff_mem _ _

theorem pt_inj {e1 e2 e3 : Fin 3 → K} (hI : Indep e1 e2 e3) {y t y' t' : K}
    (h : pt hI y t = pt hI y' t') : y = y' ∧ t = t' := by
  have hm : vec e1 e2 e3 y' t' ∈ K ∙ vec e1 e2 e3 y t := by
    have := congrArg Subtype.val h
    simp only [pt] at this
    rw [this]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  unfold vec at hc
  have h0 : (c * y - y') • e1 + (c * t - t') • e2 + (c - 1) • e3 = 0 := by
    linear_combination (norm := module) hc
  obtain ⟨h1, h2, h3⟩ := hI _ _ _ h0
  have hc1 : c = 1 := by linear_combination h3
  subst hc1
  constructor
  · linear_combination h1
  · linear_combination h2

theorem exists_functional (L : Ln K) :
    ∃ φ : (Fin 3 → K) →ₗ[K] K, ∀ w, w ∈ L.1 ↔ φ w = 0 := by
  have hL := L.2
  have hne : L.1 ≠ ⊤ := by
    intro h
    rw [h, finrank_top, Module.finrank_fin_fun] at hL
    omega
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  have hker : LinearMap.ker f ≠ ⊤ := fun h => hf0 (LinearMap.ker_eq_top.mp h)
  have h1 := Submodule.finrank_lt hker
  have h2 := Submodule.finrank_mono hle
  rw [Module.finrank_fin_fun] at h1
  have heq : L.1 = LinearMap.ker f := Submodule.eq_of_le_of_finrank_eq hle (by omega)
  exact ⟨f, fun w => by rw [heq]; rfl⟩

theorem exists_coords (H : Ln K) (O : Lines K 3) (hO : O.1 ≤ H.1) :
    ∃ e1 e2 e3 : Fin 3 → K, Indep e1 e2 e3 ∧ O.1 = K ∙ e2 ∧ e2 ∈ H.1 ∧ e3 ∈ H.1 ∧
      ∀ w ∈ H.1, ∃ α β : K, α • e2 + β • e3 = w := by
  obtain ⟨e2, he2, hO2⟩ := line_gen O
  have hH := H.2
  have hOH : O.1 < H.1 := lt_of_le_of_ne hO (fun h => by
    have h' := O.2
    rw [h] at h'
    omega)
  obtain ⟨e3, he3H, he3O⟩ := SetLike.exists_of_lt hOH
  have hHt : H.1 < ⊤ := lt_top_iff_ne_top.2 (fun h => by
    rw [h, finrank_top, Module.finrank_fin_fun] at hH
    omega)
  obtain ⟨e1, -, he1H⟩ := SetLike.exists_of_lt hHt
  have he2O : e2 ∈ O.1 := by rw [hO2]; exact Submodule.mem_span_singleton_self _
  have he2H : e2 ∈ H.1 := hO he2O
  refine ⟨e1, e2, e3, ?_, hO2, he2H, he3H, ?_⟩
  · intro a b c h
    have ha : a = 0 := by
      by_contra ha
      apply he1H
      have : a • e1 = -(b • e2 + c • e3) := by linear_combination (norm := module) h
      have hm : a • e1 ∈ H.1 := by
        rw [this]
        exact H.1.neg_mem (H.1.add_mem (H.1.smul_mem _ he2H) (H.1.smul_mem _ he3H))
      have := H.1.smul_mem a⁻¹ hm
      rwa [inv_smul_smul₀ ha] at this
    subst ha
    have hc : c = 0 := by
      by_contra hc
      apply he3O
      have : c • e3 = -(b • e2) := by linear_combination (norm := module) h
      have hm : c • e3 ∈ O.1 := by
        rw [this]
        exact O.1.neg_mem (O.1.smul_mem _ he2O)
      have := O.1.smul_mem c⁻¹ hm
      rwa [inv_smul_smul₀ hc] at this
    subst hc
    have hb : b • e2 = 0 := by linear_combination (norm := module) h
    exact ⟨rfl, (smul_eq_zero.mp hb).resolve_right he2, rfl⟩
  · set S := Submodule.span K {e2, e3}
    have hSH : S ≤ H.1 := by
      rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨he2H, he3H⟩
    have hOS : O.1 < S := by
      refine lt_of_le_of_ne ?_ (fun h => he3O (h ▸ Submodule.subset_span (by simp)))
      rw [hO2, Submodule.span_singleton_le_iff_mem]
      exact Submodule.subset_span (by simp)
    have h1 := Submodule.finrank_lt_finrank_of_lt hOS
    have h2 := Submodule.finrank_mono hSH
    rw [O.2] at h1
    have hSeq : S = H.1 := Submodule.eq_of_le_of_finrank_eq hSH (by omega)
    intro w hw
    rw [← hSeq] at hw
    exact Submodule.mem_span_pair.mp hw

end ProxGapTight.Dev.Q366PL.PartF
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL.PartF
open ProxGapTight ProxGapTight.Dev.Q366PL Polynomial
variable {K : Type} [Field K] [Fintype K]
open Classical in
/-- the points of `H` are `O` and the affine points `(0, t)` -/
theorem card_on_H (H : Ln K) (O : Lines K 3) (hO : O.1 ≤ H.1) {e1 e2 e3 : Fin 3 → K}
    (hI : Indep e1 e2 e3) (hO2 : O.1 = K ∙ e2) (he2H : e2 ∈ H.1) (he3H : e3 ∈ H.1)
    (hspan : ∀ w ∈ H.1, ∃ α β : K, α • e2 + β • e3 = w)
    (P : Lines K 3 → Prop) :
    (Finset.univ.filter fun ℓ : Lines K 3 => ℓ.1 ≤ H.1 ∧ P ℓ).card =
      (if P O then 1 else 0) + (Finset.univ.filter fun t : K => P (pt hI 0 t)).card := by
  classical
  rw [← Finset.card_filter_add_card_filter_not (p := fun ℓ : Lines K 3 => ℓ = O)]
  congr 1
  · rw [Finset.filter_filter]
    split_ifs with hP
    · rw [Finset.card_eq_one]
      refine ⟨O, ?_⟩
      ext ℓ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨⟨hO, hP⟩, rfl⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ℓ - ⟨⟨-, h⟩, rfl⟩
      exact hP h
  · rw [Finset.filter_filter]
    symm
    apply Finset.card_nbij (fun t => pt hI 0 t)
    · intro t ht
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
      refine ⟨⟨?_, ht⟩, ?_⟩
      · rw [pt_le_iff]
        unfold vec
        rw [zero_smul, add_zero]
        exact H.1.add_mem he3H (H.1.smul_mem _ he2H)
      · intro h
        have hm : vec e1 e2 e3 0 t ∈ K ∙ e2 := by
          rw [← hO2, ← h]; exact Submodule.mem_span_singleton_self _
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
        unfold vec at hc
        have := (hI 0 (c - t) (-1) (by linear_combination (norm := module) hc)).2.2
        exact one_ne_zero (neg_eq_zero.mp this)
    · intro t _ t' _ h
      exact (pt_inj hI h).2
    · intro ℓ hℓ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Set.mem_image] at hℓ ⊢
      obtain ⟨⟨hle, hP⟩, hne⟩ := hℓ
      obtain ⟨w, hw0, hℓw⟩ := line_gen ℓ
      have hwH : w ∈ H.1 := hle (by rw [hℓw]; exact Submodule.mem_span_singleton_self _)
      obtain ⟨α, β, hαβ⟩ := hspan w hwH
      have hβ : β ≠ 0 := by
        rintro rfl
        apply hne
        apply line_eq_of_le
        rw [hℓw, hO2, Submodule.span_singleton_le_iff_mem, ← hαβ, zero_smul, add_zero]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      have hℓeq : ℓ = pt hI 0 (α / β) := by
        apply Subtype.ext
        simp only [pt]
        rw [hℓw, ← Submodule.span_singleton_smul_eq (IsUnit.mk0 β hβ) (vec e1 e2 e3 0 (α / β))]
        congr 1
        rw [← hαβ]
        unfold vec
        rw [zero_smul, add_zero, smul_add, smul_smul, mul_div_cancel₀ _ hβ, add_comm]
      exact ⟨α / β, by rw [← hℓeq]; exact hP, hℓeq.symm⟩

theorem sum_le_hamming {p : ℕ} {e1 e2 e3 : Fin 3 → K} (hI : Indep e1 e2 e3)
    (v : Lines K 3 → ZMod p) :
    ∑ y : K, (Finset.univ.filter fun t : K => v (pt hI y t) ≠ 0).card ≤ hammingNorm v := by
  classical
  have h1 : ∑ y : K, (Finset.univ.filter fun t : K => v (pt hI y t) ≠ 0).card =
      (Finset.univ.filter fun yt : K × K => v (pt hI yt.1 yt.2) ≠ 0).card := by
    simp only [Finset.card_filter]
    rw [Fintype.sum_prod_type]
  rw [h1, hammingNorm]
  apply Finset.card_le_card_of_injOn (fun yt : K × K => pt hI yt.1 yt.2)
  · intro yt hyt
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hyt ⊢
    exact hyt
  · rintro ⟨y, t⟩ - ⟨y', t'⟩ - h
    simp only [Prod.mk.injEq]
    exact pt_inj hI h

end ProxGapTight.Dev.Q366PL.PartF
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL.PartF
open ProxGapTight ProxGapTight.Dev.Q366PL Polynomial
variable {K : Type} [Field K]
/-! ## Polynomials -/
/-- the affine form `b T + a Y + c` in `K[Y][T]` -/
noncomputable def lin (a b c : K) : K[X][X] := C (C b) * X + C (C a * X + C c)

theorem lin_eval (a b c y t : K) :
    ((lin a b c).map (evalRingHom y)).eval t = b * t + (a * y + c) := by
  simp [lin]

theorem pow_coeff_deg (b : K) (γ : K[X]) (hγ : γ.natDegree ≤ 1) (k : ℕ) :
    ∀ j, (((C (C b) * X + C γ) ^ k).coeff j).natDegree ≤ k - j := by
  have hdeg1 : (C (C b) * X + C γ).natDegree ≤ 1 := natDegree_linear_le
  induction k with
  | zero =>
    intro j
    rw [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ k ih =>
    intro j
    set P := (C (C b) * X + C γ) ^ k with hP
    have hPdeg : P.natDegree ≤ k := by
      rw [hP]; exact (natDegree_pow_le_of_le k hdeg1).trans (by rw [mul_one])
    have hexp : (C (C b) * X + C γ) ^ (k + 1) = C (C b) * (P * X) + P * C γ := by
      rw [pow_succ]; ring
    rw [hexp, coeff_add, coeff_C_mul, coeff_mul_C]
    cases j with
    | zero =>
      rw [coeff_mul_X_zero, mul_zero, zero_add]
      calc (P.coeff 0 * γ).natDegree ≤ (P.coeff 0).natDegree + γ.natDegree := natDegree_mul_le
        _ ≤ (k - 0) + 1 := add_le_add (ih 0) hγ
        _ = k + 1 - 0 := by omega
    | succ j =>
      rw [coeff_mul_X]
      refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_C_mul_le _ _).trans ((ih j).trans (by omega))
      · by_cases hj : j + 1 ≤ k
        · calc (P.coeff (j + 1) * γ).natDegree
              ≤ (P.coeff (j + 1)).natDegree + γ.natDegree := natDegree_mul_le
            _ ≤ (k - (j + 1)) + 1 := add_le_add (ih (j + 1)) hγ
            _ = k + 1 - (j + 1) := by omega
        · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul, natDegree_zero]
          exact Nat.zero_le _

theorem G_deg {α : Type} (S : Finset α) (κ a b c : α → K) (n : ℕ) :
    (∑ i ∈ S, C (C (κ i)) * (1 - lin (a i) (b i) (c i) ^ n)).natDegree ≤ n ∧
      ∀ j, ((∑ i ∈ S, C (C (κ i)) * (1 - lin (a i) (b i) (c i) ^ n)).coeff j).natDegree ≤ n - j := by
  constructor
  · apply natDegree_sum_le_of_forall_le
    intro i _
    refine (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans (max_le ?_ ?_))
    · rw [natDegree_one]; exact Nat.zero_le _
    · exact (natDegree_pow_le_of_le n (by unfold lin; exact natDegree_linear_le)).trans
        (by rw [mul_one])
  · intro j
    rw [finsetSum_coeff]
    apply natDegree_sum_le_of_forall_le
    intro i _
    rw [coeff_C_mul]
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [coeff_sub]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · rw [coeff_one]; split_ifs <;> simp
    · exact pow_coeff_deg (b i) (C (a i) * X + C (c i)) natDegree_linear_le n j

end ProxGapTight.Dev.Q366PL.PartF
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL.PartF
open ProxGapTight ProxGapTight.Dev.Q366PL Polynomial
variable {K : Type} [Field K]
variable [Fintype K] [DecidableEq K]
theorem gcd_deg (p : ℕ) [CharP K p] (hpq : p ∣ Fintype.card K) (g : K[X]) :
    (gcd (X ^ Fintype.card K - X) g).natDegree =
      (Finset.univ.filter fun t : K => g.eval t = 0).card := by
  classical
  have h1 : 1 < Fintype.card K := Fintype.one_lt_card
  set u : K[X] := X ^ Fintype.card K - X with hu
  have hu0 : u ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K h1
  have hsep : u.Separable := galois_poly_separable p _ hpq
  have hspl : u.Splits := by
    rw [splits_iff_card_roots, hu, FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq K h1]
    simp
  have hd : gcd u g ∣ u := gcd_dvd_left _ _
  have hd0 : gcd u g ≠ 0 := fun h => hu0 ((gcd_eq_zero_iff _ _).mp h).1
  rw [← splits_iff_card_roots.mp (Splits.of_dvd hspl hu0 hd),
    ← Multiset.toFinset_card_of_nodup (nodup_roots (hsep.of_dvd hd))]
  congr 1
  ext t
  simp only [Multiset.mem_toFinset, mem_roots hd0, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← dvd_iff_isRoot, dvd_gcd_iff, dvd_iff_isRoot, dvd_iff_isRoot]
  have hut : u.IsRoot t := by
    simp [hu, FiniteField.pow_card]
  exact ⟨fun h => h.2, fun h => ⟨hut, h⟩⟩

end ProxGapTight.Dev.Q366PL.PartF
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL.PartF
open ProxGapTight ProxGapTight.Dev.Q366PL Polynomial
variable {K : Type} [Field K] [Fintype K]
/-! ## The count -/
theorem charP_of_card (p a : ℕ) [hp : Fact p.Prime] (hK : Fintype.card K = p ^ a) :
    CharP K p ∧ p ∣ Fintype.card K := by
  have h1 : 1 < Fintype.card K := Fintype.one_lt_card
  have ha : a ≠ 0 := by
    rintro rfl
    rw [hK] at h1
    simp at h1
  obtain ⟨n, hr, hn⟩ := FiniteField.card K (ringChar K)
  have hdvd : p ∣ ringChar K := by
    have : p ∣ (ringChar K) ^ (n : ℕ) := by rw [← hn, hK]; exact dvd_pow_self p ha
    exact hp.out.dvd_of_dvd_pow this
  have heq : p = ringChar K := (Nat.prime_dvd_prime_iff_eq hp.out hr).mp hdvd
  refine ⟨?_, by rw [hK]; exact dvd_pow_self p ha⟩
  rw [heq]
  exact ringChar.charP K

omit [Fintype K] in
theorem vec_le_iff {e1 e2 e3 : Fin 3 → K} (hI : Indep e1 e2 e3) (L : Submodule K (Fin 3 → K))
    (φ : (Fin 3 → K) →ₗ[K] K) (hφ : ∀ w, w ∈ L ↔ φ w = 0) (y t : K) :
    (pt hI y t).1 ≤ L ↔ φ e2 * t + (φ e1 * y + φ e3) = 0 := by
  rw [pt_le_iff, hφ]
  have : φ (vec e1 e2 e3 y t) = φ e2 * t + (φ e1 * y + φ e3) := by
    simp only [vec, map_add, map_smul, smul_eq_mul]
    ring
  rw [this]

/-- the main count, for the affine coordinates `hI` -/
theorem main_count (p a : ℕ) [Fact p.Prime] (hK : Fintype.card K = p ^ a)
    (v : Lines K 3 → ZMod p) (hv : v ∈ C1 K p) {e1 e2 e3 : Fin 3 → K} (hI : Indep e1 e2 e3) :
    (Finset.univ.filter fun t : K => v (pt hI 0 t) ≠ 0).card *
      (Fintype.card K + 1 - (Finset.univ.filter fun t : K => v (pt hI 0 t) ≠ 0).card) ≤
      hammingNorm v := by
  classical
  obtain ⟨hchar, hpq⟩ := charP_of_card (K := K) p a hK
  have h1 : 1 < Fintype.card K := Fintype.one_lt_card
  set q := Fintype.card K with hq
  set s' : K → ℕ := fun y => (Finset.univ.filter fun t : K => v (pt hI y t) ≠ 0).card with hs'
  show s' 0 * (q + 1 - s' 0) ≤ hammingNorm v
  have hs'q : ∀ y, s' y ≤ q := fun y => by
    rw [hq, ← Finset.card_univ]; exact Finset.card_filter_le _ _
  let ι : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have hι : Function.Injective ι := ι.injective
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv
  choose φ hφ using fun L : Ln K => exists_functional L
  set G : K[X][X] := ∑ L ∈ c.support,
    C (C (ι (c L))) * (1 - lin (φ L e1) (φ L e2) (φ L e3) ^ (q - 1)) with hG
  have hGeval : ∀ y t, (G.map (evalRingHom y)).eval t = ι (v (pt hI y t)) := by
    intro y t
    rw [← hc, hG]
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, map_sum, Polynomial.map_sum,
      eval_finsetSum, Polynomial.map_mul, map_C, eval_mul, eval_C, Polynomial.map_sub,
      Polynomial.map_one, Polynomial.map_pow, eval_sub, eval_one, eval_pow, lin_eval,
      coe_evalRingHom]
    refine Finset.sum_congr rfl (fun L _ => ?_)
    unfold ind1
    rw [Set.indicator_apply]
    simp only [Set.mem_ofPred_eq]
    rw [smul_eq_mul, map_mul]
    congr 1
    by_cases hz : φ L e2 * t + (φ L e1 * y + φ L e3) = 0
    · rw [if_pos ((vec_le_iff hI L.1 (φ L) (hφ L) y t).mpr hz), hz,
        zero_pow (by omega), sub_zero, map_one]
    · rw [if_neg (fun h => hz ((vec_le_iff hI L.1 (φ L) (hφ L) y t).mp h)),
        FiniteField.pow_card_sub_one_eq_one _ hz, sub_self, map_zero]
  have hmapu : ∀ y : K, ((X ^ q - X : K[X][X]).map (evalRingHom y)) = X ^ q - X := by
    intro y; simp
  have hroots : ∀ y, (gcd ((X ^ q - X : K[X][X]).map (evalRingHom y))
      (G.map (evalRingHom y))).natDegree = q - s' y := by
    intro y
    rw [hmapu, gcd_deg p hpq]
    have hfil : (Finset.univ.filter fun t : K => (G.map (evalRingHom y)).eval t = 0) =
        Finset.univ.filter fun t : K => v (pt hI y t) = 0 := by
      apply Finset.filter_congr
      intro t _
      rw [hGeval, map_eq_zero_iff ι hι]
    rw [hfil]
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun t : K => v (pt hI y t) = 0)
    rw [Finset.card_univ] at this
    change _ = q - (Finset.univ.filter fun t : K => ¬ v (pt hI y t) = 0).card
    omega
  set s0 := s' 0 with hs0
  by_cases hs00 : s0 = 0
  · rw [hs00, zero_mul]; exact Nat.zero_le _
  have hR := R_lemma (X ^ q - X : K[X][X]) G q 1 s0 le_rfl (by omega) (hs'q 0)
    (monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1))
    (by rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [natDegree_X, natDegree_X_pow]; exact h1),
      natDegree_X_pow])
    (by
      intro i _
      rw [coeff_sub, coeff_X_pow, coeff_X]
      refine (natDegree_sub_le _ _).trans ?_
      split_ifs <;> simp)
    ((G_deg c.support (fun L => ι (c L)) (fun L => φ L e1) (fun L => φ L e2) (fun L => φ L e3)
      (q - 1)).1)
    (by
      intro i hi
      have := (G_deg c.support (fun L => ι (c L)) (fun L => φ L e1) (fun L => φ L e2)
        (fun L => φ L e3) (q - 1)).2 (q - 1 - i)
      exact this.trans (by omega))
    0 (by rw [hroots])
  simp only [hroots] at hR
  have hsum : ∑ _y : K, s0 ≤ ∑ y : K, (s' y + ((q - s' y) - (q - s0))) :=
    Finset.sum_le_sum (fun y _ => by have := hs'q y; have := hs'q 0; omega)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  have hH := sum_le_hamming hI v
  have hw : q * s0 ≤ hammingNorm v + s0 * (s0 - 1) := by
    have : ∑ y : K, s' y ≤ hammingNorm v := hH
    rw [← hq] at hsum
    omega
  have hs0q := hs'q 0
  rw [← hs0] at hs0q
  obtain ⟨k, hk⟩ : ∃ k, s0 = k + 1 := ⟨s0 - 1, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, q = s0 + r := ⟨q - s0, by omega⟩
  rw [hk] at hw hr ⊢
  rw [hr] at hw
  rw [hr, show k + 1 + r + 1 - (k + 1) = r + 1 by omega]
  rw [show k + 1 - 1 = k by omega] at hw
  nlinarith

omit [Fintype K] in
theorem vec0_mem {e1 e2 e3 : Fin 3 → K} (H : Submodule K (Fin 3 → K)) (he2H : e2 ∈ H)
    (he3H : e3 ∈ H) (t : K) : vec e1 e2 e3 0 t ∈ H := by
  unfold vec
  rw [zero_smul, add_zero]
  exact H.add_mem he3H (H.smul_mem _ he2H)

theorem sm_eq {p : ℕ} (v : Lines K 3 → ZMod p) (H : Ln K) (O : Lines K 3) (hO : O.1 ≤ H.1)
    {e1 e2 e3 : Fin 3 → K} (hI : Indep e1 e2 e3) (hO2 : O.1 = K ∙ e2) (he2H : e2 ∈ H.1)
    (he3H : e3 ∈ H.1) (hspan : ∀ w ∈ H.1, ∃ α β : K, α • e2 + β • e3 = w) :
    sm v H = (if v O ≠ 0 then 1 else 0) +
      (Finset.univ.filter fun t : K => v (pt hI 0 t) ≠ 0).card := by
  classical
  have hc := card_on_H H O hO hI hO2 he2H he3H hspan (fun ℓ => v ℓ ≠ 0)
  unfold sm
  convert hc

theorem F1_lemma (p a : ℕ) [Fact p.Prime] (K : Type) [Field K] [Fintype K]
    (hK : Fintype.card K = p ^ a) (v : Lines K 3 → ZMod p) (hv : v ∈ C1 K p) (H : Ln K) :
    sm v H = Fintype.card K + 1 ∨ sm v H * (Fintype.card K + 1 - sm v H) ≤ hammingNorm v := by
  classical
  by_cases hhole : ∃ O : Lines K 3, O.1 ≤ H.1 ∧ v O = 0
  · obtain ⟨O, hO, hvO⟩ := hhole
    obtain ⟨e1, e2, e3, hI, hO2, he2H, he3H, hspan⟩ := exists_coords H O hO
    rw [sm_eq v H O hO hI hO2 he2H he3H hspan, if_neg (by simpa using hvO), zero_add]
    right
    exact main_count p a hK v hv hI
  · push Not at hhole
    have hH := H.2
    have hne : H.1 ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hH
      omega
    obtain ⟨w, hwH, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    let O : Lines K 3 := ⟨K ∙ w, finrank_span_singleton hw0⟩
    have hO : O.1 ≤ H.1 := (Submodule.span_singleton_le_iff_mem _ _).mpr hwH
    obtain ⟨e1, e2, e3, hI, hO2, he2H, he3H, hspan⟩ := exists_coords H O hO
    left
    rw [sm_eq v H O hO hI hO2 he2H he3H hspan, if_pos (hhole O hO),
      Finset.filter_true_of_mem (fun t _ =>
        hhole _ ((pt_le_iff hI 0 t H.1).mpr (vec0_mem H.1 he2H he3H t))),
      Finset.card_univ, add_comm]

end ProxGapTight.Dev.Q366PL.PartF
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL
open ProxGapTight Polynomial
/-! ## Part F: every line is full or satisfies `s(q+1-s) ≤ w` -/
alias F1_lemma := ProxGapTight.Dev.Q366PL.PartF.F1_lemma

end ProxGapTight.Dev.Q366PL
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL.PartS
open ProxGapTight ProxGapTight.Dev.Q366PL
variable {K : Type} [Field K]
/-!
q366 planar blueprint, Part S: `cover` and `struct` (PLANAR_PLAN.md §Cover, §Struct).
-/
/-! ## Plane geometry (coordinates copied from Part F) -/
theorem line_gen (ℓ : Lines K 3) : ∃ r : Fin 3 → K, r ≠ 0 ∧ ℓ.1 = K ∙ r := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp ℓ.2
  refine ⟨v.1, fun h => hv0 (Subtype.ext h), le_antisymm (fun y hy => ?_)
    ((Submodule.span_singleton_le_iff_mem _ _).mpr v.2)⟩
  obtain ⟨c, hc⟩ := hv ⟨y, hy⟩
  have : c • v.1 = y := congrArg Subtype.val hc
  rw [← this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem line_eq_of_le {ℓ ℓ' : Lines K 3} (h : ℓ.1 ≤ ℓ'.1) : ℓ = ℓ' :=
  Subtype.ext (Submodule.eq_of_le_of_finrank_eq h (by rw [ℓ.2, ℓ'.2]))

/-- three independent vectors -/
def Indep (e1 e2 e3 : Fin 3 → K) : Prop :=
  ∀ a b c : K, a • e1 + b • e2 + c • e3 = 0 → a = 0 ∧ b = 0 ∧ c = 0

/-- the vector of the affine point `(y, t)` -/
def vec (e1 e2 e3 : Fin 3 → K) (y t : K) : Fin 3 → K := e3 + y • e1 + t • e2

theorem vec_ne {e1 e2 e3 : Fin 3 → K} (hI : Indep e1 e2 e3) (y t : K) : vec e1 e2 e3 y t ≠ 0 := by
  intro h
  have := (hI y t 1 (by rw [← h]; unfold vec; module)).2.2
  exact one_ne_zero this

/-- the affine point `(y, t)` -/
def pt {e1 e2 e3 : Fin 3 → K} (hI : Indep e1 e2 e3) (y t : K) : Lines K 3 :=
  ⟨K ∙ vec e1 e2 e3 y t, finrank_span_singleton (vec_ne hI y t)⟩

theorem pt_le_iff {e1 e2 e3 : Fin 3 → K} (hI : Indep e1 e2 e3) (y t : K)
    (L : Submodule K (Fin 3 → K)) : (pt hI y t).1 ≤ L ↔ vec e1 e2 e3 y t ∈ L :=
  Submodule.span_singleton_le_iff_mem _ _

theorem pt_inj {e1 e2 e3 : Fin 3 → K} (hI : Indep e1 e2 e3) {y t y' t' : K}
    (h : pt hI y t = pt hI y' t') : y = y' ∧ t = t' := by
  have hm : vec e1 e2 e3 y' t' ∈ K ∙ vec e1 e2 e3 y t := by
    have := congrArg Subtype.val h
    simp only [pt] at this
    rw [this]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  unfold vec at hc
  have h0 : (c * y - y') • e1 + (c * t - t') • e2 + (c - 1) • e3 = 0 := by
    linear_combination (norm := module) hc
  obtain ⟨h1, h2, h3⟩ := hI _ _ _ h0
  have hc1 : c = 1 := by linear_combination h3
  subst hc1
  constructor
  · linear_combination h1
  · linear_combination h2

theorem exists_coords (H : Ln K) (O : Lines K 3) (hO : O.1 ≤ H.1) :
    ∃ e1 e2 e3 : Fin 3 → K, Indep e1 e2 e3 ∧ O.1 = K ∙ e2 ∧ e2 ∈ H.1 ∧ e3 ∈ H.1 ∧
      ∀ w ∈ H.1, ∃ α β : K, α • e2 + β • e3 = w := by
  obtain ⟨e2, he2, hO2⟩ := line_gen O
  have hH := H.2
  have hOH : O.1 < H.1 := lt_of_le_of_ne hO (fun h => by
    have h' := O.2
    rw [h] at h'
    omega)
  obtain ⟨e3, he3H, he3O⟩ := SetLike.exists_of_lt hOH
  have hHt : H.1 < ⊤ := lt_top_iff_ne_top.2 (fun h => by
    rw [h, finrank_top, Module.finrank_fin_fun] at hH
    omega)
  obtain ⟨e1, -, he1H⟩ := SetLike.exists_of_lt hHt
  have he2O : e2 ∈ O.1 := by rw [hO2]; exact Submodule.mem_span_singleton_self _
  have he2H : e2 ∈ H.1 := hO he2O
  refine ⟨e1, e2, e3, ?_, hO2, he2H, he3H, ?_⟩
  · intro a b c h
    have ha : a = 0 := by
      by_contra ha
      apply he1H
      have : a • e1 = -(b • e2 + c • e3) := by linear_combination (norm := module) h
      have hm : a • e1 ∈ H.1 := by
        rw [this]
        exact H.1.neg_mem (H.1.add_mem (H.1.smul_mem _ he2H) (H.1.smul_mem _ he3H))
      have := H.1.smul_mem a⁻¹ hm
      rwa [inv_smul_smul₀ ha] at this
    subst ha
    have hc : c = 0 := by
      by_contra hc
      apply he3O
      have : c • e3 = -(b • e2) := by linear_combination (norm := module) h
      have hm : c • e3 ∈ O.1 := by
        rw [this]
        exact O.1.neg_mem (O.1.smul_mem _ he2O)
      have := O.1.smul_mem c⁻¹ hm
      rwa [inv_smul_smul₀ hc] at this
    subst hc
    have hb : b • e2 = 0 := by linear_combination (norm := module) h
    exact ⟨rfl, (smul_eq_zero.mp hb).resolve_right he2, rfl⟩
  · set S := Submodule.span K {e2, e3}
    have hSH : S ≤ H.1 := by
      rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨he2H, he3H⟩
    have hOS : O.1 < S := by
      refine lt_of_le_of_ne ?_ (fun h => he3O (h ▸ Submodule.subset_span (by simp)))
      rw [hO2, Submodule.span_singleton_le_iff_mem]
      exact Submodule.subset_span (by simp)
    have h1 := Submodule.finrank_lt_finrank_of_lt hOS
    have h2 := Submodule.finrank_mono hSH
    rw [O.2] at h1
    have hSeq : S = H.1 := Submodule.eq_of_le_of_finrank_eq hSH (by omega)
    intro w hw
    rw [← hSeq] at hw
    exact Submodule.mem_span_pair.mp hw

/-- the point spanned by a nonzero vector -/
def mk (u : Fin 3 → K) (hu : u ≠ 0) : Lines K 3 := ⟨K ∙ u, finrank_span_singleton hu⟩

theorem mk_le_iff (u : Fin 3 → K) (hu : u ≠ 0) (L : Submodule K (Fin 3 → K)) :
    (mk u hu).1 ≤ L ↔ u ∈ L :=
  Submodule.span_singleton_le_iff_mem _ _

theorem finrank_sup_pts {X Y : Lines K 3} (h : X ≠ Y) :
    Module.finrank K ↥(X.1 ⊔ Y.1) + 1 = 3 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq X.1 Y.1
  have hX := X.2
  have hY := Y.2
  have hle : Module.finrank K ↥(X.1 ⊓ Y.1) ≤ 1 := by
    have := Submodule.finrank_mono (inf_le_left : X.1 ⊓ Y.1 ≤ X.1)
    omega
  have h2 : Module.finrank K ↥(X.1 ⊓ Y.1) ≠ 1 := by
    intro h1'
    have e1 : X.1 ⊓ Y.1 = X.1 :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hX, h1'])
    have e2 : X.1 ⊓ Y.1 = Y.1 :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [hY, h1'])
    exact h (Subtype.ext (e1.symm.trans e2))
  rw [hX, hY] at h1
  omega

/-- the line through two distinct points -/
def join (X Y : Lines K 3) (h : X ≠ Y) : Ln K := ⟨X.1 ⊔ Y.1, finrank_sup_pts h⟩

theorem le_join_left (X Y : Lines K 3) (h : X ≠ Y) : X.1 ≤ (join X Y h).1 := le_sup_left

theorem le_join_right (X Y : Lines K 3) (h : X ≠ Y) : Y.1 ≤ (join X Y h).1 := le_sup_right

theorem line_eq_of_two {X Y : Lines K 3} (h : X ≠ Y) {H H' : Ln K} (hX : X.1 ≤ H.1)
    (hY : Y.1 ≤ H.1) (hX' : X.1 ≤ H'.1) (hY' : Y.1 ≤ H'.1) : H = H' := by
  have hs := finrank_sup_pts h
  have hH := H.2
  have hH' := H'.2
  have e1 : X.1 ⊔ Y.1 = H.1 := Submodule.eq_of_le_of_finrank_eq (sup_le hX hY) (by omega)
  have e2 : X.1 ⊔ Y.1 = H'.1 := Submodule.eq_of_le_of_finrank_eq (sup_le hX' hY') (by omega)
  exact Subtype.ext (e1.symm.trans e2)

theorem pt_eq_of_two_lines {H H' : Ln K} (h : H ≠ H') {X Y : Lines K 3} (hX : X.1 ≤ H.1)
    (hY : Y.1 ≤ H.1) (hX' : X.1 ≤ H'.1) (hY' : Y.1 ≤ H'.1) : X = Y := by
  by_contra hXY
  exact h (line_eq_of_two hXY hX hY hX' hY')

theorem exists_meet (H H' : Ln K) : ∃ X : Lines K 3, X.1 ≤ H.1 ∧ X.1 ≤ H'.1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq H.1 H'.1
  have h2 : Module.finrank K ↥(H.1 ⊔ H'.1) ≤ 3 := by
    have := Submodule.finrank_le (H.1 ⊔ H'.1)
    rwa [Module.finrank_fin_fun] at this
  have hH := H.2
  have hH' := H'.2
  have hne : H.1 ⊓ H'.1 ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at h1
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨mk w hw0, (mk_le_iff _ _ _).2 (Submodule.mem_inf.1 hw).1,
    (mk_le_iff _ _ _).2 (Submodule.mem_inf.1 hw).2⟩

theorem exists_off {L M : Ln K} (h : L ≠ M) : ∃ X : Lines K 3, X.1 ≤ L.1 ∧ ¬ X.1 ≤ M.1 := by
  have hn : ¬ L.1 ≤ M.1 := fun hle =>
    h (Subtype.ext (Submodule.eq_of_le_of_finrank_eq hle (by have := L.2; have := M.2; omega)))
  obtain ⟨x, hxL, hxM⟩ := SetLike.not_le_iff_exists.mp hn
  have hx0 : x ≠ 0 := fun h0 => hxM (h0 ▸ M.1.zero_mem)
  exact ⟨mk x hx0, (mk_le_iff _ _ _).2 hxL, fun h' => hxM ((mk_le_iff _ _ _).1 h')⟩

theorem ln_ne_top (L : Ln K) : L.1 ≠ ⊤ := by
  intro h
  have hL := L.2
  rw [h, finrank_top, Module.finrank_fin_fun] at hL
  omega

theorem exists_off_line (L : Ln K) : ∃ X : Lines K 3, ¬ X.1 ≤ L.1 := by
  obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 (ln_ne_top L))
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ L.1.zero_mem)
  exact ⟨mk x hx0, fun h' => hx ((mk_le_iff _ _ _).1 h')⟩

theorem exists_line_off (X : Lines K 3) : ∃ r : Ln K, ¬ X.1 ≤ r.1 := by
  obtain ⟨r, hr⟩ := Submodule.exists_isCompl X.1
  have h := Submodule.finrank_add_eq_of_isCompl hr
  rw [X.2, Module.finrank_fin_fun] at h
  refine ⟨⟨r, by omega⟩, fun hle => ?_⟩
  have hb : X.1 ≤ ⊥ := hr.disjoint (le_refl _) hle
  have hX := X.2
  rw [le_bot_iff.1 hb, finrank_bot] at hX
  omega

end ProxGapTight.Dev.Q366PL.PartS
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL.PartS
open ProxGapTight ProxGapTight.Dev.Q366PL
variable {K : Type} [Field K] [Fintype K]
/-! ## Counting points -/
open Classical in
/-- the points of `H` are `O` and the affine points `(0, t)` -/
theorem card_on_H (H : Ln K) (O : Lines K 3) (hO : O.1 ≤ H.1) {e1 e2 e3 : Fin 3 → K}
    (hI : Indep e1 e2 e3) (hO2 : O.1 = K ∙ e2) (he2H : e2 ∈ H.1) (he3H : e3 ∈ H.1)
    (hspan : ∀ w ∈ H.1, ∃ α β : K, α • e2 + β • e3 = w)
    (P : Lines K 3 → Prop) :
    (Finset.univ.filter fun ℓ : Lines K 3 => ℓ.1 ≤ H.1 ∧ P ℓ).card =
      (if P O then 1 else 0) + (Finset.univ.filter fun t : K => P (pt hI 0 t)).card := by
  classical
  rw [← Finset.card_filter_add_card_filter_not (p := fun ℓ : Lines K 3 => ℓ = O)]
  congr 1
  · rw [Finset.filter_filter]
    split_ifs with hP
    · rw [Finset.card_eq_one]
      refine ⟨O, ?_⟩
      ext ℓ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨⟨hO, hP⟩, rfl⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ℓ - ⟨⟨-, h⟩, rfl⟩
      exact hP h
  · rw [Finset.filter_filter]
    symm
    apply Finset.card_nbij (fun t => pt hI 0 t)
    · intro t ht
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
      refine ⟨⟨?_, ht⟩, ?_⟩
      · rw [pt_le_iff]
        unfold vec
        rw [zero_smul, add_zero]
        exact H.1.add_mem he3H (H.1.smul_mem _ he2H)
      · intro h
        have hm : vec e1 e2 e3 0 t ∈ K ∙ e2 := by
          rw [← hO2, ← h]; exact Submodule.mem_span_singleton_self _
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
        unfold vec at hc
        have := (hI 0 (c - t) (-1) (by linear_combination (norm := module) hc)).2.2
        exact one_ne_zero (neg_eq_zero.mp this)
    · intro t _ t' _ h
      exact (pt_inj hI h).2
    · intro ℓ hℓ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Set.mem_image] at hℓ ⊢
      obtain ⟨⟨hle, hP⟩, hne⟩ := hℓ
      obtain ⟨w, hw0, hℓw⟩ := line_gen ℓ
      have hwH : w ∈ H.1 := hle (by rw [hℓw]; exact Submodule.mem_span_singleton_self _)
      obtain ⟨α, β, hαβ⟩ := hspan w hwH
      have hβ : β ≠ 0 := by
        rintro rfl
        apply hne
        apply line_eq_of_le
        rw [hℓw, hO2, Submodule.span_singleton_le_iff_mem, ← hαβ, zero_smul, add_zero]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      have hℓeq : ℓ = pt hI 0 (α / β) := by
        apply Subtype.ext
        simp only [pt]
        rw [hℓw, ← Submodule.span_singleton_smul_eq (IsUnit.mk0 β hβ) (vec e1 e2 e3 0 (α / β))]
        congr 1
        rw [← hαβ]
        unfold vec
        rw [zero_smul, add_zero, smul_add, smul_smul, mul_div_cancel₀ _ hβ, add_comm]
      exact ⟨α / β, by rw [← hℓeq]; exact hP, hℓeq.symm⟩

open Classical in
theorem card_pts (H : Ln K) :
    (Finset.univ.filter fun ℓ : Lines K 3 => ℓ.1 ≤ H.1).card = Fintype.card K + 1 := by
  obtain ⟨O, hO, -⟩ := exists_meet H H
  obtain ⟨e1, e2, e3, hI, hO2, he2H, he3H, hspan⟩ := exists_coords H O hO
  have := card_on_H H O hO hI hO2 he2H he3H hspan (fun _ => True)
  simp only [and_true, if_true] at this
  rw [this]
  simp [add_comm]

theorem sm_def {p : ℕ} (v : Lines K 3 → ZMod p) (H : Ln K)
    [DecidablePred fun ℓ : Lines K 3 => ℓ.1 ≤ H.1 ∧ v ℓ ≠ 0] :
    sm v H = (Finset.univ.filter fun ℓ : Lines K 3 => ℓ.1 ≤ H.1 ∧ v ℓ ≠ 0).card := by
  unfold sm
  convert rfl

theorem cnt_def {p : ℕ} (v : Lines K 3 → ZMod p) (H : Ln K) (r : ZMod p)
    [DecidablePred fun ℓ : Lines K 3 => ℓ.1 ≤ H.1 ∧ v ℓ = r] :
    cnt v H r = (Finset.univ.filter fun ℓ : Lines K 3 => ℓ.1 ≤ H.1 ∧ v ℓ = r).card := by
  unfold cnt
  convert rfl

theorem holes_add {p : ℕ} (v : Lines K 3 → ZMod p) (H : Ln K) :
    cnt v H 0 + sm v H = Fintype.card K + 1 := by
  classical
  rw [cnt_def, sm_def, ← card_pts H, ← Finset.filter_filter, ← Finset.filter_filter]
  exact Finset.card_filter_add_card_filter_not _

end ProxGapTight.Dev.Q366PL.PartS
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL.PartS
open ProxGapTight ProxGapTight.Dev.Q366PL
variable {K : Type} [Field K] [Fintype K] {p : ℕ}
/-! ## Cover -/
theorem weight_bound (v : Lines K 3 → ZMod p) (X : Lines K 3) (hX : v X ≠ 0) (k : ℕ)
    (hk : ∀ m : Ln K, X.1 ≤ m.1 → sm v m ≤ k) :
    hammingNorm v ≤ 1 + (Fintype.card K + 1) * (k - 1) := by
  classical
  obtain ⟨r, hr⟩ := exists_line_off X
  set T := Finset.univ.filter fun ℓ : Lines K 3 => ℓ.1 ≤ r.1 with hT
  set F : Lines K 3 → Finset (Lines K 3) := fun Z =>
    Finset.univ.filter fun Y => Y ≠ X ∧ v Y ≠ 0 ∧ Y.1 ≤ X.1 ⊔ Z.1 with hF
  have hsub : (Finset.univ.filter fun Y : Lines K 3 => v Y ≠ 0) ⊆ insert X (T.biUnion F) := by
    intro Y hY
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY
    rw [Finset.mem_insert]
    by_cases hYX : Y = X
    · exact Or.inl hYX
    right
    rw [Finset.mem_biUnion]
    obtain ⟨Z, hZm, hZr⟩ := exists_meet (join X Y (Ne.symm hYX)) r
    refine ⟨Z, by simpa [hT] using hZr, ?_⟩
    have hZX : X ≠ Z := fun h => hr (h ▸ hZr)
    have he := line_eq_of_two hZX (le_join_left X Z hZX) (le_join_right X Z hZX)
      (le_join_left X Y (Ne.symm hYX)) hZm
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hYX, hY, ?_⟩
    have : Y.1 ≤ (join X Z hZX).1 := by rw [he]; exact le_join_right _ _ _
    exact this
  have hFb : ∀ Z ∈ T, (F Z).card ≤ k - 1 := by
    intro Z hZ
    have hZr : Z.1 ≤ r.1 := by simpa [hT] using hZ
    have hZX : X ≠ Z := fun h => hr (h ▸ hZr)
    have hsm := hk (join X Z hZX) (le_join_left _ _ _)
    rw [sm_def] at hsm
    have hs : insert X (F Z) ⊆
        Finset.univ.filter fun ℓ : Lines K 3 => ℓ.1 ≤ (join X Z hZX).1 ∧ v ℓ ≠ 0 := by
      intro Y hY
      rw [Finset.mem_insert] at hY
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hY with rfl | hY
      · exact ⟨le_join_left _ _ _, hX⟩
      · simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hY
        exact ⟨hY.2.2, hY.2.1⟩
    have hXn : X ∉ F Z := by simp [hF]
    have := Finset.card_le_card hs
    rw [Finset.card_insert_of_notMem hXn] at this
    omega
  have hTc : T.card = Fintype.card K + 1 := card_pts r
  calc hammingNorm v = (Finset.univ.filter fun Y : Lines K 3 => v Y ≠ 0).card := by
        unfold hammingNorm; convert rfl
    _ ≤ (insert X (T.biUnion F)).card := Finset.card_le_card hsub
    _ ≤ (T.biUnion F).card + 1 := Finset.card_insert_le _ _
    _ ≤ (∑ Z ∈ T, (F Z).card) + 1 := by
        have := Finset.card_biUnion_le (s := T) (t := F); omega
    _ ≤ T.card • (k - 1) + 1 := by
        have := Finset.sum_le_card_nsmul T (fun Z => (F Z).card) (k - 1) hFb; omega
    _ = 1 + (Fintype.card K + 1) * (k - 1) := by rw [hTc, smul_eq_mul]; ring

theorem prod_bound (s q : ℕ) (h4 : 4 ≤ s) (hs : s + 3 ≤ q) : 4 * q - 12 ≤ s * (q + 1 - s) := by
  obtain ⟨i, rfl⟩ : ∃ i, s = 4 + i := ⟨s - 4, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, q = 7 + i + j := ⟨q - 7 - i, by omega⟩
  rw [show 7 + i + j + 1 - (4 + i) = 4 + j by omega]
  have : 4 * (7 + i + j) - 12 = 16 + 4 * i + 4 * j := by omega
  rw [this]
  nlinarith

theorem long_through (p a : ℕ) [Fact p.Prime] (hK : Fintype.card K = p ^ a)
    (hq : 32 < Fintype.card K) (v : Lines K 3 → ZMod p) (hv : v ∈ C1 K p)
    (hw : hammingNorm v ≤ 4 * Fintype.card K - 22) (X : Lines K 3) (hX : v X ≠ 0) :
    ∃ m : Ln K, X.1 ≤ m.1 ∧ Fintype.card K - 2 ≤ sm v m := by
  by_contra hno
  push Not at hno
  have h3 : ∀ m : Ln K, X.1 ≤ m.1 → sm v m ≤ 3 := by
    intro m hm
    have hlt := hno m hm
    by_contra h4
    rcases F1_lemma p a K hK v hv m with h | h
    · omega
    · have := prod_bound (sm v m) (Fintype.card K) (by omega) (by omega)
      omega
  have step : ∀ k, 1 ≤ k → k ≤ 3 → (∀ m : Ln K, X.1 ≤ m.1 → sm v m ≤ k) →
      ∀ m : Ln K, X.1 ≤ m.1 → sm v m ≤ k - 1 := by
    intro k hk1 hk3 hk m hm
    have hwb := weight_bound v X hX k hk
    have hsmk := hk m hm
    by_contra hlt
    have hs : sm v m = k := by omega
    rcases F1_lemma p a K hK v hv m with h | h
    · omega
    · rw [hs] at h
      interval_cases k <;> omega
  have h0 := step 1 le_rfl (by norm_num) (step 2 (by norm_num) (by norm_num)
    (step 3 (by norm_num) le_rfl h3))
  obtain ⟨r, hr⟩ := exists_line_off X
  obtain ⟨Z, hZ, -⟩ := exists_meet r r
  have hZX : X ≠ Z := fun h => hr (h ▸ hZ)
  have hm := h0 (join X Z hZX) (le_join_left _ _ _)
  classical
  rw [sm_def] at hm
  have : 0 < (Finset.univ.filter fun ℓ : Lines K 3 =>
      ℓ.1 ≤ (join X Z hZX).1 ∧ v ℓ ≠ 0).card :=
    Finset.card_pos.mpr ⟨X, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨le_join_left _ _ _, hX⟩⟩
  omega

open Classical in
/-- support points on a line -/
noncomputable def A (v : Lines K 3 → ZMod p) (M : Ln K) : Finset (Lines K 3) :=
  Finset.univ.filter fun ℓ : Lines K 3 => ℓ.1 ≤ M.1 ∧ v ℓ ≠ 0

theorem A_card (v : Lines K 3 → ZMod p) (M : Ln K) : (A v M).card = sm v M := by
  classical
  rw [sm_def]; unfold A; convert rfl

open Classical in
theorem A_inter (v : Lines K 3 → ZMod p) {M M' : Ln K} (h : M ≠ M') :
    (A v M ∩ A v M').card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro X hX Y hY
  simp only [A, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hX hY
  exact pt_eq_of_two_lines h hX.1.1 hY.1.1 hX.2.1 hY.2.1

theorem A_sub (v : Lines K 3 → ZMod p) (M : Ln K) :
    A v M ⊆ Finset.univ.filter fun ℓ : Lines K 3 => v ℓ ≠ 0 := by
  intro X hX
  simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hX ⊢
  exact hX.2

open Classical in
theorem not_four_long (v : Lines K 3 → ZMod p) (hq : 32 < Fintype.card K)
    (hw : hammingNorm v ≤ 4 * Fintype.card K - 22) (M1 M2 M3 M4 : Ln K)
    (h12 : M1 ≠ M2) (h13 : M1 ≠ M3) (h14 : M1 ≠ M4) (h23 : M2 ≠ M3) (h24 : M2 ≠ M4)
    (h34 : M3 ≠ M4) (l1 : Fintype.card K - 2 ≤ sm v M1) (l2 : Fintype.card K - 2 ≤ sm v M2)
    (l3 : Fintype.card K - 2 ≤ sm v M3) (l4 : Fintype.card K - 2 ≤ sm v M4) : False := by
  classical
  rw [← A_card] at l1 l2 l3 l4
  have u2 := Finset.card_union_add_card_inter (A v M1) (A v M2)
  have u3 := Finset.card_union_add_card_inter (A v M1 ∪ A v M2) (A v M3)
  have u4 := Finset.card_union_add_card_inter (A v M1 ∪ A v M2 ∪ A v M3) (A v M4)
  have i3 : ((A v M1 ∪ A v M2) ∩ A v M3).card ≤ 2 := by
    rw [Finset.union_inter_distrib_right]
    have := Finset.card_union_le (A v M1 ∩ A v M3) (A v M2 ∩ A v M3)
    have := A_inter v h13
    have := A_inter v h23
    omega
  have i4 : ((A v M1 ∪ A v M2 ∪ A v M3) ∩ A v M4).card ≤ 3 := by
    rw [Finset.union_inter_distrib_right, Finset.union_inter_distrib_right]
    have := Finset.card_union_le (A v M1 ∩ A v M4 ∪ A v M2 ∩ A v M4) (A v M3 ∩ A v M4)
    have := Finset.card_union_le (A v M1 ∩ A v M4) (A v M2 ∩ A v M4)
    have := A_inter v h14
    have := A_inter v h24
    have := A_inter v h34
    omega
  have i2 := A_inter v h12
  have hsub : A v M1 ∪ A v M2 ∪ A v M3 ∪ A v M4 ⊆
      Finset.univ.filter fun ℓ : Lines K 3 => v ℓ ≠ 0 :=
    Finset.union_subset (Finset.union_subset (Finset.union_subset (A_sub v M1) (A_sub v M2))
      (A_sub v M3)) (A_sub v M4)
  have hc := Finset.card_le_card hsub
  have hwn : hammingNorm v = (Finset.univ.filter fun ℓ : Lines K 3 => v ℓ ≠ 0).card := by
    unfold hammingNorm; convert rfl
  omega

end ProxGapTight.Dev.Q366PL.PartS
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL.PartS
open ProxGapTight ProxGapTight.Dev.Q366PL
theorem cover (p a : ℕ) [Fact p.Prime] (K : Type) [Field K] [Fintype K]
    (hK : Fintype.card K = p ^ a) (hQ : 32 < p ^ a) (v : Lines K 3 → ZMod p) (hv : v ∈ C1 K p)
    (hv0 : v ≠ 0) (hw : hammingNorm v ≤ 4 * p ^ a - 22) :
    ∃ L₁ L₂ L₃ : Ln K, (∀ ℓ : Lines K 3, v ℓ ≠ 0 → ℓ.1 ≤ L₁.1 ∨ ℓ.1 ≤ L₂.1 ∨ ℓ.1 ≤ L₃.1) ∧
      cnt v L₁ 0 ≤ 3 ∧ cnt v L₂ 0 ≤ 3 ∧ cnt v L₃ 0 ≤ 3 := by
  rw [← hK] at hQ hw
  have hlong := long_through p a hK hQ v hv hw
  have hh : ∀ m : Ln K, Fintype.card K - 2 ≤ sm v m → cnt v m 0 ≤ 3 := by
    intro m hm
    have := holes_add v m
    omega
  obtain ⟨X1, hX1⟩ : ∃ X, v X ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  obtain ⟨M1, hXM1, hM1⟩ := hlong X1 hX1
  by_cases c1 : ∀ ℓ : Lines K 3, v ℓ ≠ 0 → ℓ.1 ≤ M1.1
  · exact ⟨M1, M1, M1, fun ℓ h => Or.inl (c1 ℓ h), hh _ hM1, hh _ hM1, hh _ hM1⟩
  push Not at c1
  obtain ⟨X2, hX2, hX2M1⟩ := c1
  obtain ⟨M2, hXM2, hM2⟩ := hlong X2 hX2
  have h12 : M1 ≠ M2 := fun h => hX2M1 (h ▸ hXM2)
  by_cases c2 : ∀ ℓ : Lines K 3, v ℓ ≠ 0 → ℓ.1 ≤ M1.1 ∨ ℓ.1 ≤ M2.1
  · exact ⟨M1, M2, M2, fun ℓ h => (c2 ℓ h).elim Or.inl (fun h => Or.inr (Or.inl h)),
      hh _ hM1, hh _ hM2, hh _ hM2⟩
  push Not at c2
  obtain ⟨X3, hX3, hX3M1, hX3M2⟩ := c2
  obtain ⟨M3, hXM3, hM3⟩ := hlong X3 hX3
  have h13 : M1 ≠ M3 := fun h => hX3M1 (h ▸ hXM3)
  have h23 : M2 ≠ M3 := fun h => hX3M2 (h ▸ hXM3)
  by_cases c3 : ∀ ℓ : Lines K 3, v ℓ ≠ 0 → ℓ.1 ≤ M1.1 ∨ ℓ.1 ≤ M2.1 ∨ ℓ.1 ≤ M3.1
  · exact ⟨M1, M2, M3, c3, hh _ hM1, hh _ hM2, hh _ hM3⟩
  push Not at c3
  obtain ⟨X4, hX4, hX4M1, hX4M2, hX4M3⟩ := c3
  obtain ⟨M4, hXM4, hM4⟩ := hlong X4 hX4
  exact (not_four_long v hQ hw M1 M2 M3 M4 h12 h13 (fun h => hX4M1 (h ▸ hXM4)) h23
    (fun h => hX4M2 (h ▸ hXM4)) (fun h => hX4M3 (h ▸ hXM4)) hM1 hM2 hM3 hM4).elim

end ProxGapTight.Dev.Q366PL.PartS
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL
open ProxGapTight Polynomial
/-! ## Part S: cover by three long lines, and the irreducible configurations -/
alias cover := ProxGapTight.Dev.Q366PL.PartS.cover

end ProxGapTight.Dev.Q366PL
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL.PartS
open ProxGapTight ProxGapTight.Dev.Q366PL
variable {K : Type} [Field K] [Fintype K] {p : ℕ}
/-! ## Struct -/
theorem charP_of_card (p a : ℕ) [hp : Fact p.Prime] (hK : Fintype.card K = p ^ a) :
    CharP K p ∧ p ∣ Fintype.card K := by
  have h1 : 1 < Fintype.card K := Fintype.one_lt_card
  have ha : a ≠ 0 := by
    rintro rfl
    rw [hK] at h1
    simp at h1
  obtain ⟨n, hr, hn⟩ := FiniteField.card K (ringChar K)
  have hdvd : p ∣ ringChar K := by
    have : p ∣ (ringChar K) ^ (n : ℕ) := by rw [← hn, hK]; exact dvd_pow_self p ha
    exact hp.out.dvd_of_dvd_pow this
  have heq : p = ringChar K := (Nat.prime_dvd_prime_iff_eq hp.out hr).mp hdvd
  refine ⟨?_, by rw [hK]; exact dvd_pow_self p ha⟩
  rw [heq]
  exact ringChar.charP K

open Classical in
/-- the sum of `v` over a line -/
noncomputable def lsum (v : Lines K 3 → ZMod p) (L : Ln K) : ZMod p :=
  ∑ ℓ ∈ Finset.univ.filter (fun ℓ : Lines K 3 => ℓ.1 ≤ L.1), v ℓ

theorem lsum_ind1 (hpq : (Fintype.card K : ZMod p) = 0) (H L : Ln K) :
    lsum (ind1 p H) L = 1 := by
  classical
  unfold lsum ind1
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [Finset.sum_boole, Finset.filter_filter]
  by_cases h : H = L
  · subst h
    simp only [and_self]
    have hc := card_pts (K := K) H
    rw [show (Finset.univ.filter fun ℓ : Lines K 3 => ℓ.1 ≤ H.1).card = Fintype.card K + 1 by
      convert hc]
    push_cast
    rw [hpq, zero_add]
  · have : (Finset.univ.filter fun ℓ : Lines K 3 => ℓ.1 ≤ L.1 ∧ ℓ.1 ≤ H.1).card = 1 := by
      rw [Finset.card_eq_one]
      obtain ⟨X, hXL, hXH⟩ := exists_meet L H
      refine ⟨X, ?_⟩
      ext Y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        exact pt_eq_of_two_lines (Ne.symm h) h1 hXL h2 hXH
      · rintro rfl
        exact ⟨hXL, hXH⟩
    rw [this, Nat.cast_one]

theorem lsum_const (hpq : (Fintype.card K : ZMod p) = 0) (v : Lines K 3 → ZMod p)
    (hv : v ∈ C1 K p) (L L' : Ln K) : lsum v L = lsum v L' := by
  classical
  unfold C1 at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨H, rfl⟩ := hx
    rw [lsum_ind1 hpq, lsum_ind1 hpq]
  | zero => simp [lsum]
  | add x y _ _ hx hy =>
    have e : ∀ L, lsum (x + y) L = lsum x L + lsum y L := fun L => by
      simp [lsum, Finset.sum_add_distrib]
    rw [e, e, hx, hy]
  | smul c x _ hx =>
    have e : ∀ L, lsum (c • x) L = c * lsum x L := fun L => by
      simp [lsum, Finset.mul_sum]
    rw [e, e, hx]

theorem lsum_eq_sum (v : Lines K 3 → ZMod p) (m : Ln K) (S : Finset (Lines K 3))
    (hS : ∀ x ∈ S, x.1 ≤ m.1) (hsupp : ∀ ℓ : Lines K 3, ℓ.1 ≤ m.1 → v ℓ ≠ 0 → ℓ ∈ S) :
    lsum v m = ∑ x ∈ S, v x := by
  unfold lsum
  symm
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hS x hx
  · intro x hx hxS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    by_contra h
    exact hxS (hsupp x hx h)

theorem const_contra (v : Lines K 3 → ZMod p) (L : Ln K) (hL : ∀ r, cnt v L r ≤ 3)
    (hq : 6 ≤ Fintype.card K) (E : Finset (Lines K 3)) (hE : E.card ≤ 2) (r : ZMod p)
    (h : ∀ ℓ : Lines K 3, ℓ.1 ≤ L.1 → ℓ ∉ E → v ℓ = r) : False := by
  classical
  have h1 : (Finset.univ.filter fun ℓ : Lines K 3 => ℓ.1 ≤ L.1) \ E ⊆
      Finset.univ.filter fun ℓ : Lines K 3 => ℓ.1 ≤ L.1 ∧ v ℓ = r := by
    intro ℓ hℓ
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ ⊢
    exact ⟨hℓ.1, h ℓ hℓ.1 hℓ.2⟩
  have h2 := Finset.le_card_sdiff E (Finset.univ.filter fun ℓ : Lines K 3 => ℓ.1 ≤ L.1)
  have h3 := Finset.card_le_card h1
  have h4 := hL r
  rw [cnt_def] at h4
  have h5 : (Finset.univ.filter fun ℓ : Lines K 3 => ℓ.1 ≤ L.1).card = Fintype.card K + 1 := by
    convert card_pts (K := K) L
  omega

theorem noFour_of (v : Lines K 3 → ZMod p) (L : Ln K) (h : cnt v L 0 ≤ 3)
    (hirr : ∀ r : ZMod p, r ≠ 0 → cnt v L r ≤ cnt v L 0) : ∀ r, cnt v L r ≤ 3 := by
  intro r
  by_cases hr : r = 0
  · subst hr
    exact h
  · exact (hirr r hr).trans h

theorem pigeon [NeZero p] (v : Lines K 3 → ZMod p) (L : Ln K) (hL : ∀ r, cnt v L r ≤ 3) :
    Fintype.card K + 1 ≤ 3 * p := by
  classical
  have hc : (Finset.univ.filter fun ℓ : Lines K 3 => ℓ.1 ≤ L.1).card = Fintype.card K + 1 := by
    convert card_pts (K := K) L
  rw [← hc, Finset.card_eq_sum_card_fiberwise (f := v) (t := Finset.univ)
    (fun x _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  calc ∑ r ∈ (Finset.univ : Finset (ZMod p)),
        ((Finset.univ.filter fun ℓ : Lines K 3 => ℓ.1 ≤ L.1).filter fun ℓ => v ℓ = r).card
      ≤ ∑ _r ∈ (Finset.univ : Finset (ZMod p)), 3 := Finset.sum_le_sum fun r _ => by
        rw [Finset.filter_filter, ← cnt_def]
        exact hL r
    _ = 3 * p := by simp [ZMod.card, mul_comm]

theorem a_eq_one (p a : ℕ) (hp : 2 ≤ p) (hQ : 32 < p ^ a) (h : p ^ a + 1 ≤ 3 * p) : a = 1 := by
  rcases a with _ | _ | a
  · simp at hQ
  · rfl
  · exfalso
    have h2 : p ^ 2 ≤ p ^ (a + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    by_cases hp3 : p ≤ 3
    · interval_cases p <;> omega
    · nlinarith

theorem periodic_const [Fact p.Prime] (hK1 : Fintype.card K = p) [CharP K p] (f : K → ZMod p)
    (d : K) (hd : d ≠ 0) (hf : ∀ u, f (u + d) = f u) (u : K) : f u = f 0 := by
  have hn : ∀ n : ℕ, ∀ u, f (u + n * d) = f u := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, hf, ih]
  have hinj := (ZMod.castHom (dvd_refl p) K).injective
  have hsurj : Function.Surjective (ZMod.castHom (dvd_refl p) K) :=
    ((Fintype.bijective_iff_injective_and_card (ZMod.castHom (dvd_refl p) K)).mpr
      ⟨hinj, by rw [ZMod.card, hK1]⟩).2
  obtain ⟨m, hm⟩ := hsurj (u / d)
  have hu : u = 0 + (m.val : K) * d := by
    have hc : (m.cast : K) = u / d := by rw [← hm]; rfl
    rw [ZMod.natCast_val, hc, zero_add, div_mul_cancel₀ _ hd]
  rw [hu]
  exact hn _ _

theorem f3_const [Fact p.Prime] (hK1 : Fintype.card K = p) [CharP K p] (f1 f2 f3 : K → ZMod p)
    (σ : ZMod p) (h : ∀ s t, f1 s + f2 t + f3 (s + t) = σ) (s s' : K) (hs : f1 s = f1 s')
    (hne : s ≠ s') (u : K) : f3 u = f3 0 := by
  apply periodic_const hK1 f3 (s' - s) (sub_ne_zero.2 (Ne.symm hne))
  intro x
  have e1 := h s (x - s)
  have e2 := h s' (x - s)
  rw [show s + (x - s) = x by ring] at e1
  rw [show s' + (x - s) = x + (s' - s) by ring] at e2
  linear_combination e2 - e1 + hs

end ProxGapTight.Dev.Q366PL.PartS
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL.PartS
open ProxGapTight ProxGapTight.Dev.Q366PL
variable {K : Type} [Field K]
theorem ptf_ne_zero {e2 f : Fin 3 → K} (hf : f ∉ K ∙ e2) (t : K) : f + t • e2 ≠ 0 := by
  intro h
  apply hf
  have : f = (-t) • e2 := by
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left h
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- the point `f + t e2` -/
def ptf (e2 f : Fin 3 → K) (hf : f ∉ K ∙ e2) (t : K) : Lines K 3 :=
  mk (f + t • e2) (ptf_ne_zero hf t)

theorem ptf_le {e2 f : Fin 3 → K} (hf : f ∉ K ∙ e2) (t : K) {H : Submodule K (Fin 3 → K)}
    (he2 : e2 ∈ H) (hfH : f ∈ H) : (ptf e2 f hf t).1 ≤ H :=
  (mk_le_iff _ _ _).2 (H.add_mem hfH (H.smul_mem _ he2))

theorem ptf_ne {e2 f : Fin 3 → K} (hf : f ∉ K ∙ e2) (t : K) {P : Lines K 3}
    (hP : P.1 = K ∙ e2) : ptf e2 f hf t ≠ P := by
  intro h
  apply hf
  have h1 : f + t • e2 ∈ K ∙ e2 := by
    rw [← hP, ← h]
    exact Submodule.mem_span_singleton_self _
  have h2 : t • e2 ∈ K ∙ e2 := Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  simpa using Submodule.sub_mem _ h1 h2

theorem ptf_surj {e2 f : Fin 3 → K} (hf : f ∉ K ∙ e2) {P : Lines K 3} (hP : P.1 = K ∙ e2)
    {H : Ln K} (hPH : P.1 ≤ H.1) (hfH : f ∈ H.1) (ℓ : Lines K 3) (hℓ : ℓ.1 ≤ H.1)
    (hne : ℓ ≠ P) : ∃ t, ℓ = ptf e2 f hf t := by
  have hf0 : f ≠ 0 := fun h => hf (h ▸ Submodule.zero_mem _)
  have hFP : mk f hf0 ≠ P := fun h => hf (by
    rw [← hP, ← h]
    exact Submodule.mem_span_singleton_self _)
  have hH : P.1 ⊔ K ∙ f = H.1 := by
    have hs := finrank_sup_pts (Ne.symm hFP)
    have e : (mk f hf0).1 = K ∙ f := rfl
    rw [e] at hs
    have := H.2
    exact Submodule.eq_of_le_of_finrank_eq (sup_le hPH ((mk_le_iff f hf0 _).2 hfH)) (by omega)
  obtain ⟨w, hw0, hℓw⟩ := line_gen ℓ
  have hwH : w ∈ H.1 := hℓ (by rw [hℓw]; exact Submodule.mem_span_singleton_self _)
  rw [← hH, Submodule.mem_sup] at hwH
  obtain ⟨y, hy, z, hz, hyz⟩ := hwH
  rw [hP, Submodule.mem_span_singleton] at hy
  rw [Submodule.mem_span_singleton] at hz
  obtain ⟨α, rfl⟩ := hy
  obtain ⟨β, rfl⟩ := hz
  have hβ : β ≠ 0 := by
    rintro rfl
    apply hne
    apply line_eq_of_le
    rw [hℓw, hP, Submodule.span_singleton_le_iff_mem, ← hyz, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  refine ⟨α / β, Subtype.ext ?_⟩
  show ℓ.1 = K ∙ (f + (α / β) • e2)
  rw [hℓw, ← Submodule.span_singleton_smul_eq (IsUnit.mk0 β hβ) (f + (α / β) • e2)]
  congr 1
  rw [← hyz, smul_add, smul_smul, mul_div_cancel₀ _ hβ, add_comm]

theorem off {L M : Ln K} (hLM : L ≠ M) {P : Lines K 3} (hPL : P.1 ≤ L.1) (hPM : P.1 ≤ M.1)
    (X : Lines K 3) (hXL : X.1 ≤ L.1) (hXP : X ≠ P) : ¬ X.1 ≤ M.1 :=
  fun hXM => hXP (pt_eq_of_two_lines hLM hXL hPL hXM hPM)

end ProxGapTight.Dev.Q366PL.PartS
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL.PartS
open ProxGapTight ProxGapTight.Dev.Q366PL
variable {K : Type} [Field K] [Fintype K] {p : ℕ}
theorem injA [Fact p.Prime] (hK1 : Fintype.card K = p) (hq : 6 ≤ Fintype.card K)
    (v : Lines K 3 → ZMod p) (hσ : ∀ m m' : Ln K, lsum v m = lsum v m')
    (A B C : Ln K) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (P : Lines K 3)
    (hPA : P.1 ≤ A.1) (hPB : P.1 ≤ B.1) (hPC : P.1 ≤ C.1)
    (hcov : ∀ ℓ : Lines K 3, v ℓ ≠ 0 → ℓ.1 ≤ A.1 ∨ ℓ.1 ≤ B.1 ∨ ℓ.1 ≤ C.1)
    (nC : ∀ r, cnt v C r ≤ 3) :
    ∀ ℓ ℓ' : Lines K 3, ℓ.1 ≤ A.1 → ℓ'.1 ≤ A.1 → ℓ ≠ P → ℓ' ≠ P → v ℓ = v ℓ' → ℓ = ℓ' := by
  classical
  obtain ⟨hchar, -⟩ := charP_of_card (K := K) p 1 (by rw [hK1, pow_one])
  have := hchar
  obtain ⟨e2, -, hPe⟩ := line_gen P
  have he2P : e2 ∈ P.1 := by rw [hPe]; exact Submodule.mem_span_singleton_self _
  have hPC' : P.1 < C.1 := lt_of_le_of_ne hPC (fun h => by
    have h1 := P.2
    have h2 := C.2
    rw [h] at h1
    omega)
  obtain ⟨c, hcC, hcP⟩ := SetLike.exists_of_lt hPC'
  have hsup : A.1 ⊔ B.1 = ⊤ := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq A.1 B.1
    have hA := A.2
    have hB := B.2
    have hlA := Submodule.finrank_mono (inf_le_left : A.1 ⊓ B.1 ≤ A.1)
    have hlB := Submodule.finrank_mono (inf_le_right : A.1 ⊓ B.1 ≤ B.1)
    have hlt : Module.finrank K ↥(A.1 ⊓ B.1) < 2 := by
      by_contra hge
      have e1 : A.1 ⊓ B.1 = A.1 := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
      have e2 : A.1 ⊓ B.1 = B.1 := Submodule.eq_of_le_of_finrank_eq inf_le_right (by omega)
      exact hAB (Subtype.ext (e1.symm.trans e2))
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_le (A.1 ⊔ B.1)
    rw [Module.finrank_fin_fun] at this ⊢
    omega
  have hc : c ∈ A.1 ⊔ B.1 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨a, haA, b, hbB, hab⟩ := Submodule.mem_sup.1 hc
  have hc0 : c ≠ 0 := fun h => hcP (h ▸ P.1.zero_mem)
  have hcne : mk c hc0 ≠ P := fun h => hcP (by
    rw [← h]
    exact Submodule.mem_span_singleton_self _)
  have haP : a ∉ K ∙ e2 := by
    intro ha
    rw [← hPe] at ha
    have hcB : c ∈ B.1 := hab ▸ B.1.add_mem (hPB ha) hbB
    exact hBC (line_eq_of_two hcne ((mk_le_iff _ _ _).2 hcB) hPB ((mk_le_iff _ _ _).2 hcC) hPC)
  have hbP : b ∉ K ∙ e2 := by
    intro hb
    rw [← hPe] at hb
    have hcA : c ∈ A.1 := hab ▸ A.1.add_mem haA (hPA hb)
    exact hAC (line_eq_of_two hcne ((mk_le_iff _ _ _).2 hcA) hPA ((mk_le_iff _ _ _).2 hcC) hPC)
  have hcP' : a + b ∉ K ∙ e2 := by
    rw [hab, ← hPe]
    exact hcP
  have habC : a + b ∈ C.1 := by rw [hab]; exact hcC
  have hAle : ∀ s, (ptf e2 a haP s).1 ≤ A.1 := fun s => ptf_le haP s (hPA he2P) haA
  have hBle : ∀ t, (ptf e2 b hbP t).1 ≤ B.1 := fun t => ptf_le hbP t (hPB he2P) hbB
  have hCle : ∀ u, (ptf e2 (a + b) hcP' u).1 ≤ C.1 := fun u => ptf_le hcP' u (hPC he2P) habC
  have hAne : ∀ s, ptf e2 a haP s ≠ P := fun s => ptf_ne haP s hPe
  have hBne : ∀ t, ptf e2 b hbP t ≠ P := fun t => ptf_ne hbP t hPe
  have key : ∀ s t, v (ptf e2 a haP s) + v (ptf e2 b hbP t) + v (ptf e2 (a + b) hcP' (s + t)) =
      lsum v A := by
    intro s t
    have hAB' : ptf e2 a haP s ≠ ptf e2 b hbP t := fun h =>
      off hAB hPA hPB _ (hAle s) (hAne s) (h ▸ hBle t)
    have hAC' : ptf e2 a haP s ≠ ptf e2 (a + b) hcP' (s + t) := fun h =>
      off hAC hPA hPC _ (hAle s) (hAne s) (h ▸ hCle _)
    have hBC' : ptf e2 b hbP t ≠ ptf e2 (a + b) hcP' (s + t) := fun h =>
      off hBC hPB hPC _ (hBle t) (hBne t) (h ▸ hCle _)
    set m := join _ _ hAB'
    have hCm : (ptf e2 (a + b) hcP' (s + t)).1 ≤ m.1 := by
      show K ∙ (a + b + (s + t) • e2) ≤ K ∙ (a + s • e2) ⊔ K ∙ (b + t • e2)
      rw [Submodule.span_singleton_le_iff_mem]
      have : a + b + (s + t) • e2 = (a + s • e2) + (b + t • e2) := by module
      rw [this]
      exact Submodule.add_mem_sup (Submodule.mem_span_singleton_self _)
        (Submodule.mem_span_singleton_self _)
    have hmA : m ≠ A := fun h =>
      off (Ne.symm hAB) hPB hPA _ (hBle t) (hBne t) (by rw [← h]; exact le_join_right _ _ _)
    have hmB : m ≠ B := fun h =>
      off hAB hPA hPB _ (hAle s) (hAne s) (by rw [← h]; exact le_join_left _ _ _)
    have hmC : m ≠ C := fun h =>
      off hAC hPA hPC _ (hAle s) (hAne s) (by rw [← h]; exact le_join_left _ _ _)
    have hs := lsum_eq_sum v m {ptf e2 a haP s, ptf e2 b hbP t, ptf e2 (a + b) hcP' (s + t)}
      (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact le_join_left _ _ _
        · exact le_join_right _ _ _
        · exact hCm)
      (by
        intro ℓ hℓm hℓ
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hcov ℓ hℓ with h | h | h
        · exact Or.inl (pt_eq_of_two_lines hmA hℓm (le_join_left _ _ _) h (hAle s))
        · exact Or.inr (Or.inl (pt_eq_of_two_lines hmB hℓm (le_join_right _ _ _) h (hBle t)))
        · exact Or.inr (Or.inr (pt_eq_of_two_lines hmC hℓm hCm h (hCle _))))
    rw [Finset.sum_insert (by simp [hAB', hAC']), Finset.sum_pair hBC'] at hs
    rw [hσ A m, hs]
    ring
  intro ℓ ℓ' hℓ hℓ' hℓP hℓ'P hv
  obtain ⟨s, rfl⟩ := ptf_surj haP hPe hPA haA ℓ hℓ hℓP
  obtain ⟨s', rfl⟩ := ptf_surj haP hPe hPA haA ℓ' hℓ' hℓ'P
  by_cases hss : s = s'
  · rw [hss]
  exfalso
  have hconst := f3_const hK1 (fun s => v (ptf e2 a haP s)) (fun t => v (ptf e2 b hbP t))
    (fun u => v (ptf e2 (a + b) hcP' u)) (lsum v A) key s s' hv hss
  apply const_contra v C nC hq {P} (by simp) (v (ptf e2 (a + b) hcP' 0))
  intro ℓ hℓC hℓP
  rw [Finset.mem_singleton] at hℓP
  obtain ⟨u, rfl⟩ := ptf_surj hcP' hPe hPC habC ℓ hℓC hℓP
  exact hconst u

theorem case1 (v : Lines K 3 → ZMod p) (hq : 6 ≤ Fintype.card K)
    (hσ : ∀ m m' : Ln K, lsum v m = lsum v m') (L : Ln K)
    (hcov : ∀ ℓ : Lines K 3, v ℓ ≠ 0 → ℓ.1 ≤ L.1) (nL : ∀ r, cnt v L r ≤ 3) : False := by
  classical
  obtain ⟨X, hX⟩ := exists_off_line L
  apply const_contra v L nL hq ∅ (by simp) (lsum v L)
  intro Y hY _
  have hXY : X ≠ Y := fun h => hX (h ▸ hY)
  have hmL : join X Y hXY ≠ L := fun h => hX (by rw [← h]; exact le_join_left _ _ _)
  have hs := lsum_eq_sum v (join X Y hXY) {Y}
    (by
      intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx]
      exact le_join_right _ _ _)
    (by
      intro ℓ hℓm hℓ
      rw [Finset.mem_singleton]
      exact pt_eq_of_two_lines hmL hℓm (le_join_right _ _ _) (hcov ℓ hℓ) hY)
  rw [Finset.sum_singleton] at hs
  rw [hσ L (join X Y hXY), hs]

theorem caseX (v : Lines K 3 → ZMod p) (hq : 6 ≤ Fintype.card K)
    (hσ : ∀ m m' : Ln K, lsum v m = lsum v m') (L1 L2 L3 : Ln K) (h13 : L1 ≠ L3)
    (h23 : L2 ≠ L3) (X : Lines K 3) (hX1 : X.1 ≤ L1.1) (hX2 : X.1 ≤ L2.1) (hX3 : ¬ X.1 ≤ L3.1)
    (hcov : ∀ ℓ : Lines K 3, v ℓ ≠ 0 → ℓ.1 ≤ L1.1 ∨ ℓ.1 ≤ L2.1 ∨ ℓ.1 ≤ L3.1)
    (n3 : ∀ r, cnt v L3 r ≤ 3) : False := by
  classical
  obtain ⟨Q1, hQ1a, hQ1b⟩ := exists_meet L1 L3
  obtain ⟨Q2, hQ2a, hQ2b⟩ := exists_meet L2 L3
  apply const_contra v L3 n3 hq {Q1, Q2} Finset.card_le_two (lsum v L3 - v X)
  intro Y hY hYE
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hYE
  have hY1 : ¬ Y.1 ≤ L1.1 := fun h => hYE.1 (pt_eq_of_two_lines h13 h hQ1a hY hQ1b)
  have hY2 : ¬ Y.1 ≤ L2.1 := fun h => hYE.2 (pt_eq_of_two_lines h23 h hQ2a hY hQ2b)
  have hXY : X ≠ Y := fun h => hX3 (h ▸ hY)
  have hm1 : join X Y hXY ≠ L1 := fun h => hY1 (by rw [← h]; exact le_join_right _ _ _)
  have hm2 : join X Y hXY ≠ L2 := fun h => hY2 (by rw [← h]; exact le_join_right _ _ _)
  have hm3 : join X Y hXY ≠ L3 := fun h => hX3 (by rw [← h]; exact le_join_left _ _ _)
  have hs := lsum_eq_sum v (join X Y hXY) {X, Y}
    (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact le_join_left _ _ _
      · exact le_join_right _ _ _)
    (by
      intro ℓ hℓm hℓ
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hcov ℓ hℓ with h | h | h
      · exact Or.inl (pt_eq_of_two_lines hm1 hℓm (le_join_left _ _ _) h hX1)
      · exact Or.inl (pt_eq_of_two_lines hm2 hℓm (le_join_left _ _ _) h hX2)
      · exact Or.inr (pt_eq_of_two_lines hm3 hℓm (le_join_right _ _ _) h hY))
  rw [Finset.sum_pair hXY] at hs
  rw [hσ L3 (join X Y hXY), hs]
  ring

end ProxGapTight.Dev.Q366PL.PartS
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL.PartS
open ProxGapTight ProxGapTight.Dev.Q366PL
theorem struct (p a : ℕ) [Fact p.Prime] (K : Type) [Field K] [Fintype K]
    (hK : Fintype.card K = p ^ a) (hQ : 32 < p ^ a) (v : Lines K 3 → ZMod p) (hv : v ∈ C1 K p)
    (hv0 : v ≠ 0) (L₁ L₂ L₃ : Ln K)
    (hcov : ∀ ℓ : Lines K 3, v ℓ ≠ 0 → ℓ.1 ≤ L₁.1 ∨ ℓ.1 ≤ L₂.1 ∨ ℓ.1 ≤ L₃.1)
    (h₁ : cnt v L₁ 0 ≤ 3) (h₂ : cnt v L₂ 0 ≤ 3) (h₃ : cnt v L₃ 0 ≤ 3)
    (hirr : ∀ L ∈ ({L₁, L₂, L₃} : Set (Ln K)), ∀ r : ZMod p, r ≠ 0 → cnt v L r ≤ cnt v L 0) :
    a = 1 ∧ OddType v := by
  classical
  have m1 : L₁ ∈ ({L₁, L₂, L₃} : Set (Ln K)) := Set.mem_insert _ _
  have m2 : L₂ ∈ ({L₁, L₂, L₃} : Set (Ln K)) := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have m3 : L₃ ∈ ({L₁, L₂, L₃} : Set (Ln K)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  have n1 := noFour_of v L₁ h₁ (hirr L₁ m1)
  have n2 := noFour_of v L₂ h₂ (hirr L₂ m2)
  have n3 := noFour_of v L₃ h₃ (hirr L₃ m3)
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have ha : a = 1 := a_eq_one p a hp2 hQ (hK ▸ pigeon v L₁ n1)
  subst ha
  have hK1 : Fintype.card K = p := by rw [hK, pow_one]
  have hq : 6 ≤ Fintype.card K := by rw [hK]; omega
  have hσ : ∀ m m' : Ln K, lsum v m = lsum v m' :=
    lsum_const (by rw [hK1]; exact ZMod.natCast_self p) v hv
  refine ⟨rfl, ?_⟩
  by_cases h12 : L₁ = L₂
  · subst h12
    by_cases h13 : L₁ = L₃
    · subst h13
      exact (case1 v hq hσ L₁ (fun ℓ h => by rcases hcov ℓ h with h | h | h <;> exact h) n1).elim
    · obtain ⟨X, hX1, hX3⟩ := exists_off h13
      exact (caseX v hq hσ L₁ L₁ L₃ h13 h13 X hX1 hX1 hX3 hcov n3).elim
  by_cases h13 : L₁ = L₃
  · subst h13
    obtain ⟨X, hX1, hX2⟩ := exists_off h12
    exact (caseX v hq hσ L₁ L₁ L₂ h12 h12 X hX1 hX1 hX2
      (fun ℓ h => by rcases hcov ℓ h with h | h | h <;> simp [h]) n2).elim
  by_cases h23 : L₂ = L₃
  · subst h23
    obtain ⟨X, hX2, hX1⟩ := exists_off (Ne.symm h12)
    exact (caseX v hq hσ L₂ L₂ L₁ (Ne.symm h12) (Ne.symm h12) X hX2 hX2 hX1
      (fun ℓ h => by rcases hcov ℓ h with h | h | h <;> simp [h]) n1).elim
  obtain ⟨Q, hQ1, hQ2⟩ := exists_meet L₁ L₂
  by_cases hQ3 : Q.1 ≤ L₃.1
  · refine ⟨Q, L₁, L₂, L₃, hQ1, hQ2, hQ3, h12, h13, h23, hcov, ?_⟩
    intro H hH
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hH
    rcases hH with h | h | h <;> rw [h]
    · exact injA hK1 hq v hσ L₁ L₂ L₃ h12 h13 h23 Q hQ1 hQ2 hQ3 hcov n3
    · exact injA hK1 hq v hσ L₂ L₁ L₃ (Ne.symm h12) h23 h13 Q hQ2 hQ1 hQ3
        (fun ℓ h => by rcases hcov ℓ h with h | h | h <;> simp [h]) n3
    · exact injA hK1 hq v hσ L₃ L₁ L₂ (Ne.symm h13) (Ne.symm h23) h12 Q hQ3 hQ1 hQ2
        (fun ℓ h => by rcases hcov ℓ h with h | h | h <;> simp [h]) n2
  · exact (caseX v hq hσ L₁ L₂ L₃ h13 h23 Q hQ1 hQ2 hQ3 hcov n3).elim

end ProxGapTight.Dev.Q366PL.PartS
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL
open ProxGapTight Polynomial
alias struct := ProxGapTight.Dev.Q366PL.PartS.struct

end ProxGapTight.Dev.Q366PL
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL.PartM
open ProxGapTight ProxGapTight.Dev.Q366PL
/-!
q366 planar blueprint, Part M: `plane_main`, by strong induction on the weight from the stubs
`cover` and `struct` (PLANAR_PLAN.md §Main).
-/
/-! ## Counting helpers -/
theorem bad_le {α ι : Type} (s : Finset α) (I : Finset ι) (B : ι → α → Prop)
    (hB : ∀ i ∈ I, ∀ x ∈ s, ∀ y ∈ s, B i x → B i y → x = y) (P : α → Prop) [DecidablePred P]
    (hP : ∀ x ∈ s, ¬ P x → ∃ i ∈ I, B i x) : s.card ≤ (s.filter P).card + I.card := by
  classical
  rw [← Finset.card_filter_add_card_filter_not (s := s) (p := P)]
  have : (s.filter fun x => ¬ P x).card ≤ I.card := by
    refine Finset.card_le_card_of_forall_subsingleton (fun x i => B i x) ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx
      exact hP x hx.1 hx.2
    · intro i hi x hx y hy
      exact hB i hi x (Finset.mem_filter.1 hx.1).1 y (Finset.mem_filter.1 hy.1).1 hx.2 hy.2
  omega

theorem bad3 {α : Type} (s : Finset α) (P B1 B2 B3 : α → Prop) [DecidablePred P]
    (h1 : ∀ x ∈ s, ∀ y ∈ s, B1 x → B1 y → x = y)
    (h2 : ∀ x ∈ s, ∀ y ∈ s, B2 x → B2 y → x = y)
    (h3 : ∀ x ∈ s, ∀ y ∈ s, B3 x → B3 y → x = y)
    (hP : ∀ x ∈ s, ¬ P x → B1 x ∨ B2 x ∨ B3 x) : s.card ≤ (s.filter P).card + 3 := by
  have h := bad_le s (Finset.univ : Finset (Fin 3)) (fun i => ![B1, B2, B3] i) ?_ P ?_
  · simpa using h
  · intro i _ x hx y hy
    fin_cases i
    · exact h1 x hx y hy
    · exact h2 x hx y hy
    · exact h3 x hx y hy
  · intro x hx hPx
    rcases hP x hx hPx with h | h | h
    · exact ⟨0, Finset.mem_univ _, h⟩
    · exact ⟨1, Finset.mem_univ _, h⟩
    · exact ⟨2, Finset.mem_univ _, h⟩

theorem bad2 {α : Type} (s : Finset α) (P B1 B2 : α → Prop) [DecidablePred P]
    (h1 : ∀ x ∈ s, ∀ y ∈ s, B1 x → B1 y → x = y)
    (h2 : ∀ x ∈ s, ∀ y ∈ s, B2 x → B2 y → x = y)
    (hP : ∀ x ∈ s, ¬ P x → B1 x ∨ B2 x) : s.card ≤ (s.filter P).card + 2 := by
  have h := bad_le s (Finset.univ : Finset (Fin 2)) (fun i => ![B1, B2] i) ?_ P ?_
  · simpa using h
  · intro i _ x hx y hy
    fin_cases i
    · exact h1 x hx y hy
    · exact h2 x hx y hy
  · intro x hx hPx
    rcases hP x hx hPx with h | h
    · exact ⟨0, Finset.mem_univ _, h⟩
    · exact ⟨1, Finset.mem_univ _, h⟩

end ProxGapTight.Dev.Q366PL.PartM
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL.PartM
open ProxGapTight ProxGapTight.Dev.Q366PL
variable {K : Type} [Field K] [Fintype K]
/-- the points of a subspace -/
noncomputable def pl (U : Submodule K (Fin 3 → K)) : Finset (Lines K 3) := by
  classical exact Finset.univ.filter (fun ℓ : Lines K 3 => ℓ.1 ≤ U)

theorem mem_pl (U : Submodule K (Fin 3 → K)) (ℓ : Lines K 3) : ℓ ∈ pl U ↔ ℓ.1 ≤ U := by
  classical
  unfold pl
  simp

theorem card_pl (U : Submodule K (Fin 3 → K)) (d : ℕ) (hd : Module.finrank K U = d) :
    (pl U).card = (Fintype.card K ^ d - 1) / (Fintype.card K - 1) := by
  classical
  let f : Projectivization K U → Lines K 3 := fun v =>
    ⟨v.submodule.map U.subtype, by
      rw [← v.finrank_submodule]
      exact (LinearEquiv.finrank_eq
        (Submodule.equivMapOfInjective U.subtype U.injective_subtype _).symm)⟩
  have hinj : Function.Injective f := by
    intro v w h
    apply Projectivization.submodule_injective
    have := congrArg Subtype.val h
    simp only [f] at this
    exact Submodule.map_injective_of_injective U.injective_subtype this
  have : Finite (Projectivization K U) := Finite.of_injective f hinj
  haveI : Fintype (Projectivization K U) := Fintype.ofFinite _
  have himg : (pl U) = Finset.univ.image f := by
    ext ℓ
    rw [mem_pl]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hle
      let H : Submodule K U := ℓ.1.comap U.subtype
      have hH : H.map U.subtype = ℓ.1 := by
        rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hle
      have hf1 : Module.finrank K H = 1 := by
        rw [← ℓ.2, ← hH]
        exact (LinearEquiv.finrank_eq
          (Submodule.equivMapOfInjective U.subtype U.injective_subtype H))
      refine ⟨Projectivization.mk'' H hf1, ?_⟩
      apply Subtype.ext
      simp only [f, Projectivization.submodule_mk'', hH]
    · rintro ⟨v, rfl⟩
      simp only [f]
      exact Submodule.map_subtype_le U _
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have := Projectivization.card'' K U
  rw [← Nat.card_eq_fintype_card, this, Nat.card_eq_fintype_card (α := K)]
  have hc : Nat.card U = Fintype.card K ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := U), hd, Nat.card_eq_fintype_card]
  rw [hc]

omit [Fintype K] in
theorem fr2 (H : Ln K) : Module.finrank K H.1 = 2 := by have := H.2; omega

/-- a line of the plane has `q + 1` points -/
theorem card_line (H : Ln K) : (pl H.1).card = Fintype.card K + 1 := by
  rw [card_pl H.1 2 (fr2 H)]
  have h2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  obtain ⟨q, hq⟩ : ∃ q, Fintype.card K = q + 1 := ⟨Fintype.card K - 1, by omega⟩
  rw [hq]
  apply Nat.div_eq_of_eq_mul_left (by omega)
  rw [Nat.add_sub_cancel]
  apply Nat.sub_eq_of_eq_add
  ring

omit [Fintype K] in
theorem line_eq_of_le {Y X : Lines K 3} (h : Y.1 ≤ X.1) : Y = X :=
  Subtype.ext (Submodule.eq_of_le_of_finrank_le h (by rw [Y.2, X.2]))

omit [Fintype K] in
theorem join_fr {x y : Lines K 3} (hxy : x ≠ y) : Module.finrank K ↥(x.1 ⊔ y.1) = 2 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq x.1 y.1
  have h0 : Module.finrank K ↥(x.1 ⊓ y.1) = 0 := by
    have h2 : Module.finrank K ↥(x.1 ⊓ y.1) ≤ 1 := by
      have := Submodule.finrank_mono (inf_le_left : x.1 ⊓ y.1 ≤ x.1); rw [x.2] at this
      exact this
    by_contra h0
    have e := Submodule.eq_of_le_of_finrank_le (inf_le_left : x.1 ⊓ y.1 ≤ x.1)
      (by rw [x.2]; omega)
    apply hxy
    apply line_eq_of_le
    rw [← e]; exact inf_le_right
  rw [h0, x.2, y.2] at h1; omega

omit [Fintype K] in
/-- two distinct lines share at most one point -/
theorem eq_pt {H M : Ln K} (hne : H ≠ M) {x y : Lines K 3} (hxH : x.1 ≤ H.1) (hxM : x.1 ≤ M.1)
    (hyH : y.1 ≤ H.1) (hyM : y.1 ≤ M.1) : x = y := by
  by_contra hxy
  apply hne
  apply Subtype.ext
  have e1 : x.1 ⊔ y.1 = H.1 := Submodule.eq_of_le_of_finrank_le (sup_le hxH hyH)
    (by rw [fr2 H, join_fr hxy])
  have e2 : x.1 ⊔ y.1 = M.1 := Submodule.eq_of_le_of_finrank_le (sup_le hxM hyM)
    (by rw [fr2 M, join_fr hxy])
  rw [← e1, e2]

omit [Fintype K] in
theorem ind1_le {p : ℕ} {H : Ln K} {x : Lines K 3} (h : x.1 ≤ H.1) : ind1 p H x = 1 := by
  classical
  unfold ind1; rw [Set.indicator_apply]; simp [h]

omit [Fintype K] in
theorem ind1_nle {p : ℕ} {H : Ln K} {x : Lines K 3} (h : ¬ x.1 ≤ H.1) : ind1 p H x = 0 := by
  classical
  unfold ind1; rw [Set.indicator_apply]; simp [h]

omit [Fintype K] in
theorem ln_nonempty : Nonempty (Ln K) := by
  let f : (Fin 3 → K) →ₗ[K] K := LinearMap.proj 0
  have hs : Function.Surjective f := fun c => ⟨fun _ => c, rfl⟩
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self,
    Module.finrank_fin_fun] at h
  exact ⟨⟨LinearMap.ker f, by omega⟩⟩

/-- points of `H` off a finite family of other lines -/
theorem iso_ge (H : Ln K) (F : Finset (Ln K)) (hF : H ∉ F) (P : Lines K 3 → Prop)
    [DecidablePred P] (hP : ∀ x, x.1 ≤ H.1 → (∀ M ∈ F, ¬ x.1 ≤ M.1) → P x) :
    Fintype.card K + 1 ≤ ((pl H.1).filter P).card + F.card := by
  rw [← card_line H]
  refine bad_le (pl H.1) F (fun M x => x.1 ≤ M.1) ?_ P ?_
  · intro M hM x hx y hy hxM hyM
    rw [mem_pl] at hx hy
    exact eq_pt (fun h => hF (by rw [h]; exact hM)) hx hxM hy hyM
  · intro x hx hPx
    rw [mem_pl] at hx
    by_contra hno
    push Not at hno
    exact hPx (hP x hx hno)

/-- disjoint parts of the support -/
theorem sum_le_wt {p : ℕ} {ι : Type} [Fintype ι] (v : Lines K 3 → ZMod p)
    (A : ι → Finset (Lines K 3)) (hA : ∀ i, ∀ x ∈ A i, v x ≠ 0)
    (hd : ∀ i j, i ≠ j → ∀ x ∈ A i, x ∉ A j) :
    ∑ i, (A i).card ≤ hammingNorm v := by
  classical
  rw [← Finset.card_biUnion]
  · unfold hammingNorm
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, -, hi⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hA i x hi
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    exact hd i j hij

/-- a combination of `k` distinct lines with nonzero coefficients -/
theorem comb_wt {p k : ℕ} (L : Fin k → Ln K) (c : Fin k → ZMod p) (hL : Function.Injective L)
    (hc : ∀ i, c i ≠ 0) :
    k * (Fintype.card K + 2 - k) ≤ hammingNorm (∑ i, c i • ind1 p (L i)) := by
  classical
  set v := ∑ i, c i • ind1 p (L i) with hvdef
  let A : Fin k → Finset (Lines K 3) := fun i =>
    (pl (L i).1).filter (fun x => ∀ j, j ≠ i → ¬ x.1 ≤ (L j).1)
  have hval : ∀ i, ∀ x ∈ A i, v x = c i := by
    intro i x hx
    simp only [A, Finset.mem_filter, mem_pl] at hx
    rw [hvdef, Finset.sum_apply, Finset.sum_eq_single i]
    · rw [Pi.smul_apply, ind1_le hx.1, smul_eq_mul, mul_one]
    · intro j _ hji
      rw [Pi.smul_apply, ind1_nle (hx.2 j hji), smul_zero]
    · simp
  have hsum := sum_le_wt v A (fun i x hx => by rw [hval i x hx]; exact hc i)
    (fun i j hij x hxi hxj => by
      simp only [A, Finset.mem_filter, mem_pl] at hxi hxj
      exact hxj.2 i hij hxi.1)
  have hA : ∀ i, Fintype.card K + 2 - k ≤ (A i).card := by
    intro i
    have h := iso_ge (L i) ((Finset.univ.erase i).image L) (by
        simp only [Finset.mem_image, Finset.mem_erase]
        rintro ⟨j, ⟨hji, -⟩, hj⟩
        exact hji (hL hj))
      (fun x => ∀ j, j ≠ i → ¬ x.1 ≤ (L j).1)
      (fun x _ hx j hji => hx (L j)
        (Finset.mem_image_of_mem _ (Finset.mem_erase.2 ⟨hji, Finset.mem_univ _⟩)))
    have hc' : ((Finset.univ.erase i).image L).card ≤ k - 1 := by
      refine (Finset.card_image_le).trans ?_
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have := i.2
    show _ ≤ ((pl (L i).1).filter _).card
    omega
  calc k * (Fintype.card K + 2 - k) = ∑ _i : Fin k, (Fintype.card K + 2 - k) := by simp
    _ ≤ ∑ i, (A i).card := Finset.sum_le_sum (fun i _ => hA i)
    _ ≤ hammingNorm v := hsum

/-! ## Three and four lines -/
theorem three_two {p : ℕ} (hq : 32 < Fintype.card K) (H₁ H₂ H₃ : Ln K) (α β γ : ZMod p)
    (hw : hammingNorm (α • ind1 p H₁ + β • ind1 p H₂ + γ • ind1 p H₃) ≤
      3 * Fintype.card K - 4) :
    ∃ H H' : Ln K, ∃ α' β' : ZMod p,
      α • ind1 p H₁ + β • ind1 p H₂ + γ • ind1 p H₃ = α' • ind1 p H + β' • ind1 p H' := by
  by_cases ha : α = 0
  · exact ⟨H₂, H₃, β, γ, by rw [ha]; simp⟩
  by_cases hb : β = 0
  · exact ⟨H₁, H₃, α, γ, by rw [hb]; simp⟩
  by_cases hc : γ = 0
  · exact ⟨H₁, H₂, α, β, by rw [hc]; simp⟩
  by_cases h12 : H₁ = H₂
  · subst h12; exact ⟨H₁, H₃, α + β, γ, by module⟩
  by_cases h13 : H₁ = H₃
  · subst h13; exact ⟨H₁, H₂, α + γ, β, by module⟩
  by_cases h23 : H₂ = H₃
  · subst h23; exact ⟨H₁, H₂, α, β + γ, by module⟩
  exfalso
  have h21 := Ne.symm h12
  have h31 := Ne.symm h13
  have h32 := Ne.symm h23
  have h := comb_wt (p := p) ![H₁, H₂, H₃] ![α, β, γ] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    (by intro i; fin_cases i <;> simp_all)
  have e : ∑ i, (![α, β, γ] : Fin 3 → ZMod p) i • ind1 p ((![H₁, H₂, H₃] : Fin 3 → Ln K) i) =
      α • ind1 p H₁ + β • ind1 p H₂ + γ • ind1 p H₃ := by
    simp [Fin.sum_univ_three]
  rw [e] at h
  omega

theorem four_three {p : ℕ} (hq : 32 < Fintype.card K) (H₁ H₂ H₃ H₄ : Ln K) (α β γ δ : ZMod p)
    (hw : hammingNorm (α • ind1 p H₁ + β • ind1 p H₂ + γ • ind1 p H₃ + δ • ind1 p H₄) ≤
      4 * Fintype.card K - 22) :
    Three p (α • ind1 p H₁ + β • ind1 p H₂ + γ • ind1 p H₃ + δ • ind1 p H₄) := by
  by_cases ha : α = 0
  · exact ⟨H₂, H₃, H₄, β, γ, δ, by rw [ha]; simp⟩
  by_cases hb : β = 0
  · exact ⟨H₁, H₃, H₄, α, γ, δ, by rw [hb]; simp⟩
  by_cases hc : γ = 0
  · exact ⟨H₁, H₂, H₄, α, β, δ, by rw [hc]; simp⟩
  by_cases hd : δ = 0
  · exact ⟨H₁, H₂, H₃, α, β, γ, by rw [hd]; simp⟩
  by_cases h12 : H₁ = H₂
  · subst h12; exact ⟨H₁, H₃, H₄, α + β, γ, δ, by module⟩
  by_cases h13 : H₁ = H₃
  · subst h13; exact ⟨H₁, H₂, H₄, α + γ, β, δ, by module⟩
  by_cases h14 : H₁ = H₄
  · subst h14; exact ⟨H₁, H₂, H₃, α + δ, β, γ, by module⟩
  by_cases h23 : H₂ = H₃
  · subst h23; exact ⟨H₁, H₂, H₄, α, β + γ, δ, by module⟩
  by_cases h24 : H₂ = H₄
  · subst h24; exact ⟨H₁, H₂, H₃, α, β + δ, γ, by module⟩
  by_cases h34 : H₃ = H₄
  · subst h34; exact ⟨H₁, H₂, H₃, α, β, γ + δ, by module⟩
  exfalso
  have h21 := Ne.symm h12
  have h31 := Ne.symm h13
  have h41 := Ne.symm h14
  have h32 := Ne.symm h23
  have h42 := Ne.symm h24
  have h43 := Ne.symm h34
  have h := comb_wt (p := p) ![H₁, H₂, H₃, H₄] ![α, β, γ, δ] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    (by intro i; fin_cases i <;> simp_all)
  have e : ∑ i, (![α, β, γ, δ] : Fin 4 → ZMod p) i •
      ind1 p ((![H₁, H₂, H₃, H₄] : Fin 4 → Ln K) i) =
      α • ind1 p H₁ + β • ind1 p H₂ + γ • ind1 p H₃ + δ • ind1 p H₄ := by
    simp [Fin.sum_univ_four]
  rw [e] at h
  omega

/-! ## Removing a line lowers the weight -/
theorem cnt_eq {p : ℕ} (v : Lines K 3 → ZMod p) (H : Ln K) (r : ZMod p) :
    cnt v H r = ((pl H.1).filter (fun x => v x = r)).card := by
  classical
  unfold cnt pl
  rw [Finset.filter_filter]

open Classical in
theorem wt_split {p : ℕ} (w : Lines K 3 → ZMod p) (H : Ln K) :
    hammingNorm w + cnt w H 0 =
      (Finset.univ.filter (fun x : Lines K 3 => ¬ x.1 ≤ H.1 ∧ w x ≠ 0)).card +
        (pl H.1).card := by
  classical
  rw [cnt_eq]
  have e1 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun x : Lines K 3 => w x ≠ 0)) (p := fun x => x.1 ≤ H.1)
  have s1 : (Finset.univ.filter (fun x : Lines K 3 => w x ≠ 0)).filter (fun x => x.1 ≤ H.1) =
      (pl H.1).filter (fun x => ¬ w x = 0) := by
    ext x; simp [mem_pl, and_comm]
  have s2 : (Finset.univ.filter (fun x : Lines K 3 => w x ≠ 0)).filter (fun x => ¬ x.1 ≤ H.1) =
      Finset.univ.filter (fun x : Lines K 3 => ¬ x.1 ≤ H.1 ∧ w x ≠ 0) := by
    ext x; simp [and_comm]
  rw [s1, s2] at e1
  have e3 : hammingNorm w = (Finset.univ.filter (fun x : Lines K 3 => w x ≠ 0)).card := by
    unfold hammingNorm; congr 1
  rw [e3]
  have e4 : ((pl H.1).filter fun x => w x = 0).card +
      ((pl H.1).filter fun x => ¬ w x = 0).card = (pl H.1).card :=
    Finset.card_filter_add_card_filter_not _
  omega

theorem wt_drop {p : ℕ} (v : Lines K 3 → ZMod p) (H : Ln K) (r : ZMod p) :
    hammingNorm (v - r • ind1 p H) + cnt v H r = hammingNorm v + cnt v H 0 := by
  classical
  have a1 := wt_split (v - r • ind1 p H) H
  have a2 := wt_split v H
  have e1 : cnt (v - r • ind1 p H) H 0 = cnt v H r := by
    rw [cnt_eq, cnt_eq]
    congr 1
    apply Finset.filter_congr
    intro x hx
    rw [mem_pl] at hx
    simp only [Pi.sub_apply, Pi.smul_apply, ind1_le hx, smul_eq_mul, mul_one, sub_eq_zero]
  have e2 : Finset.univ.filter (fun x : Lines K 3 => ¬ x.1 ≤ H.1 ∧ (v - r • ind1 p H) x ≠ 0) =
      Finset.univ.filter (fun x : Lines K 3 => ¬ x.1 ≤ H.1 ∧ v x ≠ 0) := by
    apply Finset.filter_congr
    intro x _
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      simpa [ind1_nle h1] using h2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      simpa [ind1_nle h1] using h2
  rw [e1, e2] at a1
  omega

/-! ## Odd type, indexed form -/
/-- `OddType` with the three lines indexed by `Fin 3` -/
def OddF {p : ℕ} (v : Lines K 3 → ZMod p) : Prop :=
  ∃ S : Lines K 3, ∃ H : Fin 3 → Ln K, (∀ j, S.1 ≤ (H j).1) ∧ (∀ i j, i ≠ j → H i ≠ H j) ∧
    (∀ ℓ : Lines K 3, v ℓ ≠ 0 → ∃ j, ℓ.1 ≤ (H j).1) ∧
    ∀ j, ∀ ℓ ℓ' : Lines K 3, ℓ.1 ≤ (H j).1 → ℓ'.1 ≤ (H j).1 → ℓ ≠ S → ℓ' ≠ S →
      v ℓ = v ℓ' → ℓ = ℓ'

omit [Fintype K] in
theorem oddF_of {p : ℕ} {v : Lines K 3 → ZMod p} (h : OddType v) : OddF v := by
  obtain ⟨S, H₁, H₂, H₃, h1, h2, h3, h12, h13, h23, hcov, hinj⟩ := h
  have h21 := Ne.symm h12
  have h31 := Ne.symm h13
  have h32 := Ne.symm h23
  refine ⟨S, ![H₁, H₂, H₃], ?_, ?_, ?_, ?_⟩
  · intro j; fin_cases j <;> simpa
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  · intro ℓ hℓ
    rcases hcov ℓ hℓ with h | h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
    · exact ⟨2, by simpa using h⟩
  · intro j
    fin_cases j
    · exact hinj H₁ (by simp)
    · exact hinj H₂ (by simp)
    · exact hinj H₃ (by simp)

omit [Fintype K] in
theorem odd_of_F {p : ℕ} {v : Lines K 3 → ZMod p} (h : OddF v) : OddType v := by
  obtain ⟨S, H, hS, hd, hcov, hinj⟩ := h
  refine ⟨S, H 0, H 1, H 2, hS 0, hS 1, hS 2, hd 0 1 (by decide), hd 0 2 (by decide),
    hd 1 2 (by decide), ?_, ?_⟩
  · intro ℓ hℓ
    obtain ⟨j, hj⟩ := hcov ℓ hℓ
    fin_cases j
    · exact Or.inl hj
    · exact Or.inr (Or.inl hj)
    · exact Or.inr (Or.inr hj)
  · intro M hM
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hM
    rcases hM with rfl | rfl | rfl
    · exact hinj 0
    · exact hinj 1
    · exact hinj 2

theorem odd_wt {p : ℕ} {v : Lines K 3 → ZMod p} (h : OddF v) :
    3 * (Fintype.card K - 1) ≤ hammingNorm v := by
  classical
  obtain ⟨S, H, hS, hd, -, hinj⟩ := h
  let A : Fin 3 → Finset (Lines K 3) := fun j => (pl (H j).1).filter (fun x => x ≠ S ∧ v x ≠ 0)
  have hsum := sum_le_wt v A (fun j x hx => (Finset.mem_filter.1 hx).2.2)
    (fun i j hij x hxi hxj => by
      simp only [A, Finset.mem_filter, mem_pl] at hxi hxj
      exact hxi.2.1 (eq_pt (hd i j hij) hxi.1 hxj.1 (hS i) (hS j)))
  have hA : ∀ j, Fintype.card K - 1 ≤ (A j).card := by
    intro j
    have h := bad2 (pl (H j).1) (fun x => x ≠ S ∧ v x ≠ 0) (fun x => x = S)
      (fun x => x ≠ S ∧ v x = 0)
      (fun x _ y _ hx hy => hx.trans hy.symm)
      (fun x hx y hy hx' hy' => hinj j x y ((mem_pl _ _).1 hx) ((mem_pl _ _).1 hy) hx'.1 hy'.1
        (hx'.2.trans hy'.2.symm))
      (fun x _ hx => by
        by_cases hxS : x = S
        · exact Or.inl hxS
        · exact Or.inr ⟨hxS, by by_contra h0; exact hx ⟨hxS, h0⟩⟩)
    rw [card_line] at h
    have h' : Fintype.card K + 1 ≤ (A j).card + 2 := by convert h using 3
    omega
  calc 3 * (Fintype.card K - 1) = ∑ _j : Fin 3, (Fintype.card K - 1) := by simp
    _ ≤ ∑ j, (A j).card := Finset.sum_le_sum (fun j _ => hA j)
    _ ≤ hammingNorm v := hsum

/-- adding a line to an odd-type word -/
theorem odd_step {p : ℕ} (hq : 32 < Fintype.card K) {v v' : Lines K 3 → ZMod p} (h : OddF v')
    (L : Ln K) (r : ZMod p) (hr : r ≠ 0) (hv : v = v' + r • ind1 p L)
    (hw : hammingNorm v ≤ 4 * Fintype.card K - 22) : OddF v := by
  classical
  obtain ⟨S, H, hS, hd, hcov, hinj⟩ := h
  have hval : ∀ x, v x = v' x + r * ind1 p L x := by
    intro x; rw [hv]; rfl
  by_cases hL : ∃ j0, L = H j0
  · obtain ⟨j0, rfl⟩ := hL
    refine ⟨S, H, hS, hd, ?_, ?_⟩
    · intro ℓ hℓ
      by_cases h0 : v' ℓ = 0
      · refine ⟨j0, ?_⟩
        by_contra hn
        rw [hval, h0, ind1_nle hn] at hℓ
        simp at hℓ
      · exact hcov ℓ h0
    · intro j ℓ ℓ' hℓ hℓ' hS1 hS2 heq
      have hi : ind1 p (H j0) ℓ = ind1 p (H j0) ℓ' := by
        by_cases hj : j = j0
        · subst hj; rw [ind1_le hℓ, ind1_le hℓ']
        · have n1 : ¬ ℓ.1 ≤ (H j0).1 := fun h' => hS1 (eq_pt (hd j j0 hj) hℓ h' (hS j) (hS j0))
          have n2 : ¬ ℓ'.1 ≤ (H j0).1 :=
            fun h' => hS2 (eq_pt (hd j j0 hj) hℓ' h' (hS j) (hS j0))
          rw [ind1_nle n1, ind1_nle n2]
      rw [hval, hval, hi] at heq
      exact hinj j ℓ ℓ' hℓ hℓ' hS1 hS2 (add_right_cancel heq)
  · exfalso
    push Not at hL
    let A : Option (Fin 3) → Finset (Lines K 3) := fun o =>
      match o with
      | none => (pl L.1).filter (fun x => ∀ j, ¬ x.1 ≤ (H j).1)
      | some j => (pl (H j).1).filter (fun x => x ≠ S ∧ v' x ≠ 0 ∧ ¬ x.1 ≤ L.1)
    have hA : ∀ o, ∀ x ∈ A o, v x ≠ 0 := by
      intro o x hx
      rcases o with _ | j
      · simp only [A, Finset.mem_filter, mem_pl] at hx
        have h0 : v' x = 0 := by
          by_contra h0
          obtain ⟨j, hj⟩ := hcov x h0
          exact hx.2 j hj
        rw [hval, h0, ind1_le hx.1]
        simpa using hr
      · simp only [A, Finset.mem_filter, mem_pl] at hx
        rw [hval, ind1_nle hx.2.2.2]
        simpa using hx.2.2.1
    have hdis : ∀ o o', o ≠ o' → ∀ x ∈ A o, x ∉ A o' := by
      intro o o' hoo x hx hx'
      rcases o with _ | i <;> rcases o' with _ | j
      · exact hoo rfl
      · simp only [A, Finset.mem_filter, mem_pl] at hx hx'
        exact hx.2 j hx'.1
      · simp only [A, Finset.mem_filter, mem_pl] at hx hx'
        exact hx'.2 i hx.1
      · simp only [A, Finset.mem_filter, mem_pl] at hx hx'
        have hij : i ≠ j := fun e => hoo (by rw [e])
        exact hx.2.1 (eq_pt (hd i j hij) hx.1 hx'.1 (hS i) (hS j))
    have hsum := sum_le_wt v A hA hdis
    rw [Fintype.sum_option] at hsum
    have b0 : Fintype.card K + 1 ≤ (A none).card + 3 := by
      have h := bad3 (pl L.1) (fun x => ∀ j, ¬ x.1 ≤ (H j).1) (fun x => x.1 ≤ (H 0).1)
        (fun x => x.1 ≤ (H 1).1) (fun x => x.1 ≤ (H 2).1)
        (fun x hx y hy h1 h2 => eq_pt (hL 0) ((mem_pl _ _).1 hx) h1 ((mem_pl _ _).1 hy) h2)
        (fun x hx y hy h1 h2 => eq_pt (hL 1) ((mem_pl _ _).1 hx) h1 ((mem_pl _ _).1 hy) h2)
        (fun x hx y hy h1 h2 => eq_pt (hL 2) ((mem_pl _ _).1 hx) h1 ((mem_pl _ _).1 hy) h2)
        (fun x _ hx => by
          push Not at hx
          obtain ⟨j, hj⟩ := hx
          fin_cases j
          · exact Or.inl hj
          · exact Or.inr (Or.inl hj)
          · exact Or.inr (Or.inr hj))
      rw [card_line] at h
      exact h
    have bj : ∀ j, Fintype.card K + 1 ≤ (A (some j)).card + 3 := by
      intro j
      have h := bad3 (pl (H j).1) (fun x => x ≠ S ∧ v' x ≠ 0 ∧ ¬ x.1 ≤ L.1) (fun x => x = S)
        (fun x => x ≠ S ∧ v' x = 0) (fun x => x.1 ≤ L.1)
        (fun x _ y _ hx hy => hx.trans hy.symm)
        (fun x hx y hy hx' hy' => hinj j x y ((mem_pl _ _).1 hx) ((mem_pl _ _).1 hy) hx'.1 hy'.1
          (hx'.2.trans hy'.2.symm))
        (fun x hx y hy h1 h2 =>
          eq_pt (Ne.symm (hL j)) ((mem_pl _ _).1 hx) h1 ((mem_pl _ _).1 hy) h2)
        (fun x _ hx => by
          by_cases hxS : x = S
          · exact Or.inl hxS
          · by_cases h0 : v' x = 0
            · exact Or.inr (Or.inl ⟨hxS, h0⟩)
            · by_cases hxL : x.1 ≤ L.1
              · exact Or.inr (Or.inr hxL)
              · exact absurd ⟨hxS, h0, hxL⟩ hx)
      rw [card_line] at h
      exact h
    rw [Fin.sum_univ_three] at hsum
    have := bj 0
    have := bj 1
    have := bj 2
    omega

/-! ## The induction -/
theorem item2 (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a) (hK : Fintype.card K = p ^ a) :
    ∀ n, ∀ v : Lines K 3 → ZMod p, v ∈ C1 K p → hammingNorm v = n →
      hammingNorm v ≤ 4 * p ^ a - 22 → Three p v ∨ (a = 1 ∧ OddF v) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro v hv hn hw
  by_cases hv0 : v = 0
  · obtain ⟨H⟩ := (ln_nonempty : Nonempty (Ln K))
    exact Or.inl ⟨H, H, H, 0, 0, 0, by rw [hv0]; simp⟩
  obtain ⟨L₁, L₂, L₃, hcov, h₁, h₂, h₃⟩ := cover p a K hK hQ v hv hv0 hw
  by_cases hred : ∃ L ∈ ({L₁, L₂, L₃} : Set (Ln K)), ∃ r : ZMod p, r ≠ 0 ∧
      cnt v L 0 < cnt v L r
  · obtain ⟨L, -, r, hr, hlt⟩ := hred
    have hd := wt_drop v L r
    have hv' : v - r • ind1 p L ∈ C1 K p :=
      Submodule.sub_mem _ hv (Submodule.smul_mem _ r (Submodule.subset_span ⟨L, rfl⟩))
    have hvv : v = (v - r • ind1 p L) + r • ind1 p L := by abel
    rcases ih (hammingNorm (v - r • ind1 p L)) (by omega) _ hv' rfl (by omega) with
      ⟨H₁, H₂, H₃, α, β, γ, he⟩ | ⟨ha, hodd⟩
    · left
      rw [he] at hvv
      rw [hvv] at hw ⊢
      exact four_three (by omega) H₁ H₂ H₃ L α β γ r (by rw [hK]; exact hw)
    · right
      exact ⟨ha, odd_step (by omega) hodd L r hr hvv (by rw [hK]; exact hw)⟩
  · push Not at hred
    obtain ⟨ha, hodd⟩ := struct p a K hK hQ v hv hv0 L₁ L₂ L₃ hcov h₁ h₂ h₃ hred
    exact Or.inr ⟨ha, oddF_of hodd⟩

end ProxGapTight.Dev.Q366PL.PartM
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL.PartM
open ProxGapTight ProxGapTight.Dev.Q366PL
theorem plane_main (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a)
    (h49 : p ^ a ≠ 49) (h121 : p ^ a ≠ 121)
    (K : Type) [Field K] [Fintype K] (hK : Fintype.card K = p ^ a)
    (v : Lines K 3 → ZMod p)
    (hv : v ∈ Submodule.span (ZMod p) (Set.range fun H :
        {H : Submodule K (Fin 3 → K) // Module.finrank K H + 1 = 3} =>
          Set.indicator {ℓ : Lines K 3 | ℓ.1 ≤ H.1} (fun _ => (1 : ZMod p)))) :
    (hammingNorm v ≤ 3 * p ^ a - 4 →
      ∃ H H' : {H : Submodule K (Fin 3 → K) // Module.finrank K H + 1 = 3}, ∃ α β : ZMod p,
        v = α • Set.indicator {ℓ : Lines K 3 | ℓ.1 ≤ H.1} (fun _ => (1 : ZMod p)) +
          β • Set.indicator {ℓ : Lines K 3 | ℓ.1 ≤ H'.1} (fun _ => (1 : ZMod p))) ∧
    (hammingNorm v ≤ 4 * p ^ a - 22 →
      (∃ H₁ H₂ H₃ : {H : Submodule K (Fin 3 → K) // Module.finrank K H + 1 = 3},
        ∃ α β γ : ZMod p,
          v = α • Set.indicator {ℓ : Lines K 3 | ℓ.1 ≤ H₁.1} (fun _ => (1 : ZMod p)) +
            β • Set.indicator {ℓ : Lines K 3 | ℓ.1 ≤ H₂.1} (fun _ => (1 : ZMod p)) +
            γ • Set.indicator {ℓ : Lines K 3 | ℓ.1 ≤ H₃.1} (fun _ => (1 : ZMod p))) ∨
      (a = 1 ∧ ∃ S : Lines K 3,
        ∃ H₁ H₂ H₃ : {H : Submodule K (Fin 3 → K) // Module.finrank K H + 1 = 3},
          S.1 ≤ H₁.1 ∧ S.1 ≤ H₂.1 ∧ S.1 ≤ H₃.1 ∧ H₁ ≠ H₂ ∧ H₁ ≠ H₃ ∧ H₂ ≠ H₃ ∧
          (∀ ℓ : Lines K 3, v ℓ ≠ 0 → ℓ.1 ≤ H₁.1 ∨ ℓ.1 ≤ H₂.1 ∨ ℓ.1 ≤ H₃.1) ∧
          ∀ H ∈ ({H₁, H₂, H₃} : Set {H : Submodule K (Fin 3 → K) // Module.finrank K H + 1 = 3}),
            ∀ ℓ ℓ' : Lines K 3, ℓ.1 ≤ H.1 → ℓ'.1 ≤ H.1 → ℓ ≠ S → ℓ' ≠ S → v ℓ = v ℓ' → ℓ = ℓ')) := by
  have hv1 : v ∈ C1 K p := hv
  have hq : 32 < Fintype.card K := by rw [hK]; exact hQ
  have h2 := item2 p a hQ hK (hammingNorm v) v hv1 rfl
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · rcases h2 (by omega) with ⟨H₁, H₂, H₃, α, β, γ, he⟩ | ⟨-, hodd⟩
    · rw [he] at hw ⊢
      exact three_two hq H₁ H₂ H₃ α β γ (by rw [hK]; exact hw)
    · have := odd_wt hodd
      omega
  · rcases h2 hw with h | ⟨ha, hodd⟩
    · exact Or.inl h
    · exact Or.inr ⟨ha, odd_of_F hodd⟩

end ProxGapTight.Dev.Q366PL.PartM
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366PL
open ProxGapTight Polynomial
/-! ## Part M: the plane statement -/

end ProxGapTight.Dev.Q366PL
end

theorem solution : type_of% @ProxGapTight.Dev.Q366PL.PartM.plane_main :=
  @ProxGapTight.Dev.Q366PL.PartM.plane_main
