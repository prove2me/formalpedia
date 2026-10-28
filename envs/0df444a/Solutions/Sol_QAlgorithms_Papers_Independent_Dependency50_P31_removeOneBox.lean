-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P31.removeOneBox
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:12:31.027928+00:00
-- url     : https://prove2.me/submissions/cc8b06a1-a1a6-4586-baa8-d2d9d46ed7a9

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P31

noncomputable section

namespace RBAux

open QAlgorithms QAlgorithms.Schur QAlgorithms.Papers.Independent.Dependency50.P31
open scoped ComplexConjugate
open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- extension of a permutation of `Fin k` to `Fin n` fixing `≥ k`. -/
def ext {n k : ℕ} (hk : k ≤ n) (σ : Equiv.Perm (Fin k)) : Equiv.Perm (Fin n) :=
  σ.extendDomain (Fin.castLEquiv hk)

lemma ext_lt {n k : ℕ} (hk : k ≤ n) (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    ext hk σ (Fin.castLE hk i) = Fin.castLE hk (σ i) := by
  have := Equiv.Perm.extendDomain_apply_image σ (Fin.castLEquiv hk) i
  simpa [ext] using this

lemma ext_ge {n k : ℕ} (hk : k ≤ n) (σ : Equiv.Perm (Fin k)) (i : Fin n) (h : k ≤ i.val) :
    ext hk σ i = i := by
  unfold ext
  exact Equiv.Perm.extendDomain_apply_not_subtype σ (Fin.castLEquiv hk) (by omega)

lemma ext_mul {n k : ℕ} (hk : k ≤ n) (σ τ : Equiv.Perm (Fin k)) :
    ext hk (σ * τ) = ext hk σ * ext hk τ := by
  unfold ext; rw [Equiv.Perm.extendDomain_mul]

lemma ext_sign {n k : ℕ} (hk : k ≤ n) (σ : Equiv.Perm (Fin k)) :
    Equiv.Perm.sign (ext hk σ) = Equiv.Perm.sign σ := by
  unfold ext; rw [Equiv.Perm.sign_extendDomain]

lemma ext_inj {n k : ℕ} (hk : k ≤ n) : Function.Injective (ext (n := n) hk) := by
  intro σ τ h
  ext i
  have := congrArg (fun π => (π (Fin.castLE hk i)).val) h
  simpa [ext_lt] using this

lemma ext_surj {n k : ℕ} (hk : k ≤ n) (π : Equiv.Perm (Fin n))
    (hπ : ∀ i : Fin n, k ≤ i.val → π i = i) : ∃ σ, ext hk σ = π := by
  have h₁ : ∀ x, (π x).val < k ↔ x.val < k := by
    intro x
    constructor
    · intro h
      by_contra hx
      have := hπ x (by omega)
      rw [this] at h; omega
    · intro hx
      by_contra h
      have h' := hπ (π x) (by omega)
      have := π.injective h'
      rw [this] at h; omega
  refine ⟨(Fin.castLEquiv hk).symm.permCongr (π.subtypePerm h₁), ?_⟩
  apply Equiv.ext
  intro b
  by_cases hb : b.val < k
  · unfold ext
    rw [Equiv.Perm.extendDomain_apply_subtype (p := fun i : Fin n => i.val < k) _ _ hb]
    simp [Equiv.permCongr_apply]
  · rw [ext_ge hk _ b (by omega), hπ b (by omega)]

lemma forall_split {n k : ℕ} (hk : k ≤ n) (P : Fin n → Prop) :
    (∀ i, P i) ↔ (∀ i : Fin k, P (Fin.castLE hk i)) ∧
      (∀ i : Fin (n-k), P ⟨k + i.val, by omega⟩) := by
  constructor
  · intro h; exact ⟨fun i => h _, fun i => h _⟩
  · rintro ⟨h1, h2⟩ i
    by_cases hi : i.val < k
    · have := h1 ⟨i.val, hi⟩
      exact this
    · have := h2 ⟨i.val - k, by omega⟩
      have e : (⟨k + (i.val - k), by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
      rwa [e] at this

/-- splitting a word. -/
def W {d n k : ℕ} (hk : k ≤ n) : Word n d ≃ Word k d × Word (n-k) d where
  toFun y := (leftWord k hk y, rightWord k hk y)
  invFun p := fun i => if h : i.val < k then p.1 ⟨i.val, h⟩ else p.2 ⟨i.val - k, by omega⟩
  left_inv y := by
    funext i
    by_cases h : i.val < k
    · simp [h, leftWord]
    · simp only [h, dite_false, rightWord]
      congr 1; exact Fin.ext (by show k + (i.val - k) = i.val; omega)
  right_inv p := by
    ext i
    · simp [leftWord]
    · simp [rightWord]

@[simp] lemma left_W {d n k : ℕ} (hk : k ≤ n) (p : Word k d × Word (n-k) d) :
    leftWord k hk ((W hk).symm p) = p.1 := congrArg Prod.fst ((W hk).apply_symm_apply p)

@[simp] lemma right_W {d n k : ℕ} (hk : k ≤ n) (p : Word k d × Word (n-k) d) :
    rightWord k hk ((W hk).symm p) = p.2 := congrArg Prod.snd ((W hk).apply_symm_apply p)

lemma word_eq_iff {d n k : ℕ} (hk : k ≤ n) (x y : Word n d) :
    x = y ↔ rightWord k hk x = rightWord k hk y ∧ leftWord k hk x = leftWord k hk y := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    have : W hk x = W hk y := Prod.ext h2 h1
    exact (W hk).injective this

lemma liftLeft_apply {d n k : ℕ} (hk : k ≤ n) (P : Matrix (Word k d) (Word k d) ℂ)
    (x y : Word n d) : liftLeft k hk P x y =
      if rightWord k hk x = rightWord k hk y then P (leftWord k hk x) (leftWord k hk y) else 0 :=
  rfl

lemma liftLeft_one {d n k : ℕ} (hk : k ≤ n) :
    liftLeft (d := d) k hk 1 = 1 := by
  ext x y
  rw [liftLeft_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp
  · have := word_eq_iff hk x y
    rw [if_neg h]
    split_ifs with h1 h2
    · exact absurd (this.2 ⟨h1, h2⟩) h
    · rfl
    · rfl

lemma liftLeft_mul {d n k : ℕ} (hk : k ≤ n) (P Q : Matrix (Word k d) (Word k d) ℂ) :
    liftLeft k hk (P * Q) = liftLeft k hk P * liftLeft k hk Q := by
  ext x z
  rw [Matrix.mul_apply, ← (W hk).symm.sum_comp, Fintype.sum_prod_type]
  simp only [liftLeft_apply, left_W, right_W, Matrix.mul_apply, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  by_cases h : rightWord k hk x = rightWord k hk z
  · rw [if_pos h, Finset.sum_eq_single (rightWord k hk z)]
    · simp [h]
    · intro b _ hb; simp [hb]
    · simp
  · rw [if_neg h]
    symm
    apply Finset.sum_eq_zero; intro y _
    apply Finset.sum_eq_zero; intro u _
    split_ifs with h1 h2
    · subst h1; exact absurd h2 h
    · rfl
    · rfl

lemma ext_ge' {n k : ℕ} (hk : k ≤ n) (σ : Equiv.Perm (Fin k)) (i : ℕ) (h : k + i < n) :
    ext hk σ ⟨k + i, h⟩ = ⟨k + i, h⟩ := ext_ge hk σ _ (by simp)

lemma lw_apply {d n k : ℕ} (hk : k ≤ n) (y : Word n d) (i : Fin k) :
    leftWord k hk y i = y (Fin.castLE hk i) := rfl

lemma rw_apply {d n k : ℕ} (hk : k ≤ n) (y : Word n d) (i : Fin (n-k)) :
    rightWord k hk y i = y ⟨k + i.val, by omega⟩ := rfl

lemma tp_key {d n k : ℕ} (hk : k ≤ n) (σ : Equiv.Perm (Fin k)) (x y : Word n d) :
    y = x ∘ (ext hk σ).symm ↔
      rightWord k hk y = rightWord k hk x ∧ leftWord k hk y = leftWord k hk x ∘ σ.symm := by
  rw [Equiv.eq_comp_symm, Equiv.eq_comp_symm, funext_iff, forall_split hk, funext_iff, funext_iff,
    and_comm]
  simp only [Function.comp_apply, ext_lt, ext_ge', lw_apply, rw_apply]

lemma tp_ext {d n k : ℕ} (hk : k ≤ n) (σ : Equiv.Perm (Fin k)) :
    tensorPermutation d n (ext hk σ) = liftLeft k hk (tensorPermutation d k σ) := by
  ext y x
  rw [liftLeft_apply]
  simp only [tensorPermutation, Matrix.of_apply]
  by_cases h1 : rightWord k hk y = rightWord k hk x <;>
    by_cases h2 : leftWord k hk y = leftWord k hk x ∘ σ.symm <;>
    simp [tp_key, h1, h2]

lemma liftLeft_smul {d n k : ℕ} (hk : k ≤ n) (c : ℂ) (P : Matrix (Word k d) (Word k d) ℂ) :
    liftLeft k hk (c • P) = c • liftLeft k hk P := by
  ext x y
  rw [Matrix.smul_apply, liftLeft_apply, liftLeft_apply]
  split_ifs <;> simp

lemma liftLeft_sum {d n k : ℕ} (hk : k ≤ n) {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Word k d) (Word k d) ℂ) :
    liftLeft k hk (∑ i ∈ s, f i) = ∑ i ∈ s, liftLeft k hk (f i) := by
  ext x y
  rw [Matrix.sum_apply, liftLeft_apply]
  simp only [liftLeft_apply]
  split_ifs
  · exact Matrix.sum_apply _ _ _ _
  · simp

lemma prefixCells_prefix {n k j : ℕ} (hk : k ≤ n) (hj : j ≤ k) (t : Filling n) :
    prefixCells (tableauPrefix t k hk) j = prefixCells t j := by
  ext c
  simp only [prefixCells, tableauPrefix, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i.val, by omega⟩, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i.val, by omega⟩, hi, rfl⟩

lemma group_map {n k j : ℕ} (hk : k ≤ n) (hj : j ≤ k) (t : Filling n) (f : ℕ × ℕ → ℕ) :
    (Finset.univ.filter fun π : Equiv.Perm (Fin n) =>
      (∀ i : Fin n, j ≤ i.val → π i = i) ∧ ∀ i : Fin n, f (t (π i)) = f (t i)) =
    (Finset.univ.filter fun σ : Equiv.Perm (Fin k) =>
      (∀ i : Fin k, j ≤ i.val → σ i = i) ∧
        ∀ i : Fin k, f (tableauPrefix t k hk (σ i)) = f (tableauPrefix t k hk i)).map
      ⟨ext hk, ext_inj hk⟩ := by
  ext π
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨σ, rfl⟩ := ext_surj hk π (fun i hi => h1 i (by omega))
    refine ⟨σ, ⟨fun i hi => ?_, fun i => ?_⟩, rfl⟩
    · have := h1 (Fin.castLE hk i) hi
      rw [ext_lt] at this
      exact Fin.castLE_injective hk this
    · have := h2 (Fin.castLE hk i)
      rw [ext_lt] at this
      exact this
  · rintro ⟨σ, ⟨h1, h2⟩, rfl⟩
    refine ⟨fun i hi => ?_, fun i => ?_⟩
    · by_cases hik : i.val < k
      · have e : i = Fin.castLE hk ⟨i.val, hik⟩ := rfl
        rw [e, ext_lt, h1 _ hi]
      · exact ext_ge hk σ i (by omega)
    · by_cases hik : i.val < k
      · have e : i = Fin.castLE hk ⟨i.val, hik⟩ := rfl
        rw [e, ext_lt]
        exact h2 _
      · rw [ext_ge hk σ i (by omega)]

lemma young_lift {d n k j : ℕ} (hk : k ≤ n) (hj : j ≤ k) (t : Filling n) :
    youngPrefix (tensorPermutation d n) t j =
      liftLeft k hk (youngPrefix (tensorPermutation d k) (tableauPrefix t k hk) j) := by
  unfold youngPrefix
  rw [liftLeft_smul, prefixCells_prefix hk hj, liftLeft_sum]
  congr 1
  rw [rowGroup, group_map hk hj t Prod.fst, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro a _
  rw [liftLeft_sum, columnGroup, group_map hk hj t Prod.snd, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Function.Embedding.coeFn_mk]
  rw [liftLeft_smul, ← ext_mul, tp_ext, ext_sign]

lemma rec_lift {d n k : ℕ} (hk : k ≤ n) (t : Filling n) :
    ∀ j ≤ k, projectionRec (youngPrefix (tensorPermutation d n) t) j =
      liftLeft k hk (projectionRec (youngPrefix (tensorPermutation d k) (tableauPrefix t k hk)) j) := by
  intro j
  induction j with
  | zero => intro _; simp only [projectionRec]; rw [liftLeft_one]
  | succ j ih =>
    intro hj
    simp only [projectionRec]
    split_ifs
    · exact young_lift hk hj t
    · rw [ih (by omega), young_lift hk hj t, liftLeft_mul, liftLeft_mul]

/-- contraction of the right factor. -/
def contr {d n k : ℕ} (hk : k ≤ n) (ψ : H d n) (w : H d (n-k)) : H d k :=
  WithLp.toLp 2 (fun u => ∑ v, ψ ((W hk).symm (u, v)) * conj (w v))

lemma contr_apply {d n k : ℕ} (hk : k ≤ n) (ψ : H d n) (w : H d (n-k)) (u : Word k d) :
    contr hk ψ w u = ∑ v, ψ ((W hk).symm (u, v)) * conj (w v) := rfl

lemma coord_sum {ι κ : Type*} [Fintype κ] (s : Finset ι) (f : ι → EuclideanSpace ℂ κ) (x : κ) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  simp [WithLp.ofLp_sum, Finset.sum_apply]

lemma contr_decomp {d n k : ℕ} (hk : k ≤ n) {r : ℕ} (c : Fin r → ℂ) (a : Fin r → H d k)
    (b : Fin r → H d (n-k)) (w : H d (n-k)) :
    contr hk (∑ i, c i • joinAt k hk (a i) (b i)) w = ∑ i, (c i * inner ℂ w (b i)) • a i := by
  ext u
  rw [contr_apply, coord_sum]
  simp only [coord_sum, PiLp.smul_apply, smul_eq_mul, joinAt, PiLp.toLp_apply, left_W, right_W,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [PiLp.inner_apply, RCLike.inner_apply, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  ring

lemma act_lift_apply {d n k : ℕ} (hk : k ≤ n) (Q : Matrix (Word k d) (Word k d) ℂ) (φ : H d n)
    (u : Word k d) (v : Word (n-k) d) :
    act (liftLeft k hk Q) φ ((W hk).symm (u, v)) = ∑ u', Q u u' * φ ((W hk).symm (u', v)) := by
  simp only [act, PiLp.toLp_apply, Matrix.mulVec, dotProduct]
  rw [← (W hk).symm.sum_comp, Fintype.sum_prod_type]
  simp only [liftLeft_apply, left_W, right_W, ite_mul, zero_mul]
  apply Finset.sum_congr rfl
  intro u' _
  rw [Finset.sum_ite_eq]
  simp

lemma contr_lift {d n k : ℕ} (hk : k ≤ n) (Q : Matrix (Word k d) (Word k d) ℂ) (φ : H d n)
    (w : H d (n-k)) : contr hk (act (liftLeft k hk Q) φ) w = act Q (contr hk φ w) := by
  ext u
  rw [contr_apply]
  simp only [act_lift_apply]
  simp only [act, PiLp.toLp_apply, Matrix.mulVec, dotProduct]
  simp only [contr, PiLp.toLp_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u' _
  apply Finset.sum_congr rfl
  intro v _
  ring

lemma schmidt_mem {d n k : ℕ} (hk : k ≤ n) (Q : Matrix (Word k d) (Word k d) ℂ) (φ psi : H d n)
    (hpsi : psi = act (liftLeft k hk Q) φ) (s : PhysicalSchmidtDecomposition psi k hk)
    (i : Fin s.rank) (hc : 0 < s.coeff i) :
    s.left i ∈ LinearMap.range (Matrix.toEuclideanLin Q) := by
  have h1 : contr hk psi (s.right i) = (s.coeff i : ℂ) • s.left i := by
    rw [congrArg (fun z => contr hk z (s.right i)) s.reconstruct, contr_decomp]
    have ho := orthonormal_iff_ite.mp s.right_orthonormal i
    simp only [ho, mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
    rw [Finset.sum_ite_eq]
    simp
  have h2 : contr hk psi (s.right i) = act Q (contr hk φ (s.right i)) := by
    exact (congrArg (fun z => contr hk z (s.right i)) hpsi).trans (contr_lift _ _ _ _)
  have hc' : (s.coeff i : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨(s.coeff i : ℂ)⁻¹ • contr hk φ (s.right i), ?_⟩
  rw [map_smul]
  change (s.coeff i : ℂ)⁻¹ • act Q (contr hk φ (s.right i)) = s.left i
  rw [← h2, h1, smul_smul, inv_mul_cancel₀ hc', one_smul]

lemma young_one {d : ℕ} (t : Filling 1) : youngPrefix (tensorPermutation d 1) t 1 = 1 := by
  have hp : ∀ π : Equiv.Perm (Fin 1), π = 1 := fun π => Equiv.ext (fun i => Subsingleton.elim _ _)
  have hR : rowGroup t 1 = {1} := by
    ext π; rw [hp π]; simp [rowGroup]
  have hC : columnGroup t 1 = {1} := by
    ext π; rw [hp π]; simp [columnGroup]
  have hP : prefixCells t 1 = {t 0} := by
    ext c; simp [prefixCells]
  have h1 : tensorPermutation d 1 1 = 1 := by
    ext y x; simp only [tensorPermutation, Matrix.of_apply, Matrix.one_apply]; rfl
  unfold youngPrefix
  rw [hR, hC, hP]
  simp [cellHook, h1, Finset.filter_singleton]

lemma space_one {d m : ℕ} (hm : m = 1) (t : Filling m) (x : H d m) : x ∈ tableauSpace d t := by
  subst hm
  have h : tableauProjector d t = 1 := by
    simp only [tableauProjector, projectionRec]
    rw [if_pos (by omega), young_one]
  refine ⟨x, ?_⟩
  rw [h]
  change act 1 x = x
  simp [act]

lemma rec_succ {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : ℕ → Matrix ι ι ℂ) (j : ℕ) (hj : 3 ≤ j) :
    projectionRec Y j = projectionRec Y (j-1) * Y j * projectionRec Y (j-1) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j-1, by omega⟩
  rw [Nat.add_sub_cancel]
  simp only [projectionRec]
  rw [if_neg (by omega)]

lemma act_act {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    act A (act B ψ) = act (A * B) ψ := by
  simp [act, Matrix.mulVec_mulVec]

end RBAux

open QAlgorithms QAlgorithms.Schur QAlgorithms.Papers.Independent.Dependency50.P31
open scoped ComplexConjugate
open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] Classical.propDecidable

theorem solution {d n : ℕ} (hn : 2 ≤ n) (nu : Schur.Partition d n)
    (t : Filling n) (ht : IsTableau nu.val t) (psi : H d n)
    (hpsi : psi ∈ tableauSpace d t) (s : PhysicalSchmidtDecomposition psi (n-1) (by omega)) :
    ∀ i, 0 < s.coeff i → s.left i ∈ tableauSpace d (tableauPrefix t (n-1) (by omega)) := by
  intro i hi
  by_cases h2 : n = 2
  · exact RBAux.space_one (by omega) _ _
  · obtain ⟨v, hv⟩ := hpsi
    have hk : n - 1 ≤ n := by omega
    have hT : tableauProjector d t =
        liftLeft (n-1) hk (tableauProjector d (tableauPrefix t (n-1) hk)) *
          youngPrefix (tensorPermutation d n) t n *
          liftLeft (n-1) hk (tableauProjector d (tableauPrefix t (n-1) hk)) := by
      unfold tableauProjector
      rw [RBAux.rec_succ _ n (by omega), RBAux.rec_lift hk t (n-1) le_rfl]
    have hpsi' : psi = act (liftLeft (n-1) hk (tableauProjector d (tableauPrefix t (n-1) hk)))
        (act (youngPrefix (tensorPermutation d n) t n *
          liftLeft (n-1) hk (tableauProjector d (tableauPrefix t (n-1) hk))) v) := by
      rw [← hv, RBAux.act_act, ← Matrix.mul_assoc, ← hT]
      rfl
    exact RBAux.schmidt_mem hk _ _ psi hpsi' s i hi
