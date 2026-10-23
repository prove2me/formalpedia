-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P18.subadditivity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:42:16.214005+00:00
-- url     : https://prove2.me/submissions/94a25f9a-e2a7-4252-a4a5-0d29439464a2

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder
open Matrix

local notation "Γ" => QAlgorithms.Papers.Independent.Information100.P04.gamma

variable {A B C E : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype E]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E]

theorem x8_bound_aux {α : Type} [Fintype α] [DecidableEq α] (W : Matrix α α ℂ) (hW : W * Wᴴ = 1)
    (d : α → ℝ) (c : ℝ) (hc : ∀ k, |d k| ≤ c) :
    ((c : ℂ) • (1 : Matrix α α ℂ) + W * diagonal (fun k => (d k : ℂ)) * Wᴴ).PosSemidef ∧
    ((c : ℂ) • (1 : Matrix α α ℂ) - W * diagonal (fun k => (d k : ℂ)) * Wᴴ).PosSemidef := by
  have h1 : (c : ℂ) • (1 : Matrix α α ℂ) = W * diagonal (fun _ => (c : ℂ)) * Wᴴ := by
    rw [← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hW]
  rw [h1, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add, ← Matrix.sub_mul, ← Matrix.mul_sub,
    diagonal_sub]
  constructor
  · refine PosSemidef.mul_mul_conjTranspose_same ?_ W
    rw [posSemidef_diagonal_iff]
    intro k
    have := (abs_le.1 (hc k)).1
    rw [← Complex.ofReal_add]
    exact Complex.zero_le_real.2 (by linarith)
  · refine PosSemidef.mul_mul_conjTranspose_same ?_ W
    rw [posSemidef_diagonal_iff]
    intro k
    have := (abs_le.1 (hc k)).2
    rw [← Complex.ofReal_sub]
    exact Complex.zero_le_real.2 (by linarith)

theorem x8_bound {α : Type} [Fintype α] [DecidableEq α] (H : Matrix α α ℂ) (hH : H.IsHermitian) :
    ∃ c : ℝ, 0 ≤ c ∧ ((c : ℂ) • (1 : Matrix α α ℂ) + H).PosSemidef ∧
      ((c : ℂ) • (1 : Matrix α α ℂ) - H).PosSemidef := by
  have hs : H = (hH.eigenvectorUnitary : Matrix α α ℂ) *
      diagonal (fun k => ((hH.eigenvalues k : ℝ) : ℂ)) * (hH.eigenvectorUnitary : Matrix α α ℂ)ᴴ := by
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  refine ⟨∑ k, |hH.eigenvalues k|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  have key := x8_bound_aux _ (Unitary.coe_mul_star_self hH.eigenvectorUnitary) _ _ fun k =>
    Finset.single_le_sum (f := fun k => |hH.eigenvalues k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
  rw [← hs] at key
  exact key

/-- the real value set of the correlation gauge -/
def x8G (s : Matrix (A × B) (A × B) ℂ) : Set ℝ :=
  {r | ∃ k l v, GammaFeasible s k l v ∧ r = (Matrix.kronecker k l).trace.re}

theorem x8_gamma_herm (s : Matrix (A × B) (A × B) ℂ) (hs : s.IsHermitian) : (Γ s).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, QAlgorithms.Papers.Independent.Information100.P04.gamma]
  exact hs.apply _ _

theorem x8_gamma_one (c : ℂ) : Γ (c • (1 : Matrix (A × B) (A × B) ℂ)) = c • 1 := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [QAlgorithms.Papers.Independent.Information100.P04.gamma, Matrix.smul_apply, Matrix.one_apply,
    Prod.mk.injEq]
  by_cases h1 : a = a' <;> by_cases h2 : b = b' <;> simp [h1, h2, eq_comm]

theorem x8_G_ne (s : Matrix (A × B) (A × B) ℂ) (hs : s.IsHermitian) : (x8G s).Nonempty := by
  obtain ⟨c, hc, h1, h2⟩ := x8_bound (Γ s) (x8_gamma_herm s hs)
  have hk : (Matrix.kronecker ((c : ℂ) • (1 : Matrix A A ℂ)) (1 : Matrix B B ℂ)) =
      (c : ℂ) • (1 : Matrix (A × B) (A × B) ℂ) := by
    simp only [Matrix.kronecker]
    rw [smul_kronecker, one_kronecker_one]
  have hH : ((c : ℂ) • (1 : Matrix A A ℂ)).IsHermitian := by
    simp [IsHermitian, conjTranspose_smul]
  have hH' : ((c : ℂ) • (1 : Matrix (A × B) (A × B) ℂ)).IsHermitian := by
    simp [IsHermitian, conjTranspose_smul]
  refine ⟨_, (c : ℂ) • (1 : Matrix A A ℂ), 1, (c : ℂ) • (1 : Matrix (A × B) (A × B) ℂ),
    ⟨hH, isHermitian_one, hH', ?_, ?_, ?_, ?_⟩, rfl⟩
  · show (Γ (_ + s)).PosSemidef
    have : Γ ((c : ℂ) • (1 : Matrix (A × B) (A × B) ℂ) + s) = Γ ((c : ℂ) • 1) + Γ s := rfl
    rw [this, x8_gamma_one]; exact h1
  · have : Γ ((c : ℂ) • (1 : Matrix (A × B) (A × B) ℂ) - s) = Γ ((c : ℂ) • 1) - Γ s := rfl
    rw [this, x8_gamma_one]; exact h2
  · rw [hk]
    have : ((c : ℂ) • (1 : Matrix (A × B) (A × B) ℂ)).PosSemidef :=
      PosSemidef.one.smul (by exact_mod_cast hc)
    exact this.add this
  · rw [hk, sub_self]; exact PosSemidef.zero


theorem x8_feas_psd {s : Matrix (A × B) (A × B) ℂ} {k : Matrix A A ℂ} {l : Matrix B B ℂ}
    {v : Matrix (A × B) (A × B) ℂ} (h : GammaFeasible s k l v) : (Matrix.kronecker k l).PosSemidef := by
  have h2 := (h.2.2.2.2.2.1.add h.2.2.2.2.2.2).smul (show (0 : ℂ) ≤ (1 / 2 : ℂ) by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]; exact Complex.zero_le_real.2 (by norm_num))
  convert h2 using 1
  rw [add_add_sub_cancel, ← two_smul ℂ, smul_smul]
  norm_num

theorem x8_tr_psd {α : Type} [Fintype α] {M : Matrix α α ℂ} (hM : M.PosSemidef) :
    0 ≤ M.trace.re ∧ M.trace.im = 0 := by
  have := hM.trace_nonneg
  rw [Complex.nonneg_iff] at this
  exact ⟨this.1, this.2.symm⟩

theorem x8_G_nonneg {s : Matrix (A × B) (A × B) ℂ} {r : ℝ} (hr : r ∈ x8G s) : 0 ≤ r := by
  obtain ⟨k, l, v, h, rfl⟩ := hr
  exact (x8_tr_psd (x8_feas_psd h)).1

theorem x8_cg_le {s : Matrix (A × B) (A × B) ℂ} {r : ℝ} (hr : r ∈ x8G s) :
    correlationGauge s ≤ (r : EReal) := by
  obtain ⟨k, l, v, h, rfl⟩ := hr
  exact sInf_le ⟨k, l, v, h, rfl⟩

theorem x8_cg_eq (s : Matrix (A × B) (A × B) ℂ) (hne : (x8G s).Nonempty) :
    correlationGauge s = ((sInf (x8G s) : ℝ) : EReal) := by
  have hb : BddBelow (x8G s) := ⟨0, fun r hr => x8_G_nonneg hr⟩
  apply le_antisymm
  · refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    induction c using EReal.rec with
    | bot => exact absurd hc (not_lt_bot)
    | top => exact le_top
    | coe c =>
      have hc' : sInf (x8G s) < c := EReal.coe_lt_coe_iff.1 hc
      obtain ⟨r, hr, hrc⟩ := exists_lt_of_csInf_lt hne hc'
      exact (x8_cg_le hr).trans (EReal.coe_le_coe_iff.2 hrc.le)
  · refine le_sInf ?_
    rintro _ ⟨k, l, v, h, rfl⟩
    exact EReal.coe_le_coe_iff.2 (csInf_le hb ⟨k, l, v, h, rfl⟩)


def x8e : (A × C) × (B × E) → (A × B) × (C × E) := fun i => ((i.1.1, i.2.1), (i.1.2, i.2.2))

theorem x8_bt_sub (X : Matrix (A × B) (A × B) ℂ) (Y : Matrix (C × E) (C × E) ℂ) :
    bipartiteTensor X Y = (Matrix.kronecker X Y).submatrix x8e x8e := rfl

theorem x8_bt_psd {X : Matrix (A × B) (A × B) ℂ} {Y : Matrix (C × E) (C × E) ℂ} (hX : X.PosSemidef)
    (hY : Y.PosSemidef) : (bipartiteTensor X Y).PosSemidef := by
  rw [x8_bt_sub]; exact (hX.kronecker hY).submatrix _

theorem x8_kron_herm {α β : Type} [Fintype α] [Fintype β] {X : Matrix α α ℂ} {Y : Matrix β β ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) : (Matrix.kronecker X Y).IsHermitian := by
  unfold IsHermitian
  simp only [Matrix.kronecker]
  rw [conjTranspose_kronecker, hX.eq, hY.eq]

theorem x8_bt_herm {X : Matrix (A × B) (A × B) ℂ} {Y : Matrix (C × E) (C × E) ℂ} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) : (bipartiteTensor X Y).IsHermitian := by
  rw [x8_bt_sub]; exact (x8_kron_herm hX hY).submatrix _

theorem x8_pm (X v : Matrix (A × B) (A × B) ℂ) (X' v' : Matrix (C × E) (C × E) ℂ)
    (h1 : (X + v).PosSemidef) (h2 : (X - v).PosSemidef) (h3 : (X' + v').PosSemidef)
    (h4 : (X' - v').PosSemidef) :
    (bipartiteTensor X X' + bipartiteTensor v v').PosSemidef ∧
      (bipartiteTensor X X' - bipartiteTensor v v').PosSemidef := by
  have hh : (0 : ℂ) ≤ (1 / 2 : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]; exact Complex.zero_le_real.2 (by norm_num)
  constructor
  · have e : bipartiteTensor X X' + bipartiteTensor v v' = (1 / 2 : ℂ) •
        (bipartiteTensor (X + v) (X' + v') + bipartiteTensor (X - v) (X' - v')) := by
      ext i j; simp only [bipartiteTensor, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
    rw [e]; exact ((x8_bt_psd h1 h3).add (x8_bt_psd h2 h4)).smul hh
  · have e : bipartiteTensor X X' - bipartiteTensor v v' = (1 / 2 : ℂ) •
        (bipartiteTensor (X + v) (X' - v') + bipartiteTensor (X - v) (X' + v')) := by
      ext i j; simp only [bipartiteTensor, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
    rw [e]; exact ((x8_bt_psd h1 h4).add (x8_bt_psd h2 h3)).smul hh

theorem x8_prod_mem {σ : Matrix (A × B) (A × B) ℂ} {τ : Matrix (C × E) (C × E) ℂ} {r r' : ℝ}
    (hr : r ∈ x8G σ) (hr' : r' ∈ x8G τ) : r * r' ∈ x8G (bipartiteTensor σ τ) := by
  obtain ⟨k, l, v, h, rfl⟩ := hr
  obtain ⟨k', l', v', h', rfl⟩ := hr'
  have hkl : Matrix.kronecker (Matrix.kronecker k k') (Matrix.kronecker l l') =
      bipartiteTensor (Matrix.kronecker k l) (Matrix.kronecker k' l') := by
    ext i j; simp only [bipartiteTensor, Matrix.kronecker, kroneckerMap_apply]; ring
  have hg : ∀ (X : Matrix (A × B) (A × B) ℂ) (Y : Matrix (C × E) (C × E) ℂ),
      Γ (bipartiteTensor X Y) = bipartiteTensor (Γ X) (Γ Y) := fun _ _ => rfl
  obtain ⟨hk, hl, hv, h1, h2, h3, h4⟩ := h
  obtain ⟨hk', hl', hv', h1', h2', h3', h4'⟩ := h'
  have g1 := x8_pm (Γ v) (Γ σ) (Γ v') (Γ τ) h1 h2 h1' h2'
  have g2 := x8_pm _ _ _ _ h3 h4 h3' h4'
  refine ⟨Matrix.kronecker k k', Matrix.kronecker l l', bipartiteTensor v v',
    ⟨x8_kron_herm hk hk', x8_kron_herm hl hl', x8_bt_herm hv hv', ?_, ?_, ?_, ?_⟩, ?_⟩
  · show (Γ (bipartiteTensor v v') + Γ (bipartiteTensor σ τ)).PosSemidef
    rw [hg, hg]; exact g1.1
  · show (Γ (bipartiteTensor v v') - Γ (bipartiteTensor σ τ)).PosSemidef
    rw [hg, hg]; exact g1.2
  · rw [hkl]; exact g2.1
  · rw [hkl]; exact g2.2
  · have i1 := (x8_tr_psd (x8_feas_psd ⟨hk, hl, hv, h1, h2, h3, h4⟩)).2
    have i2 := (x8_tr_psd (x8_feas_psd ⟨hk', hl', hv', h1', h2', h3', h4'⟩)).2
    have : (Matrix.kronecker (Matrix.kronecker k k') (Matrix.kronecker l l')).trace =
        (Matrix.kronecker k l).trace * (Matrix.kronecker k' l').trace := by
      simp only [Matrix.kronecker, trace_kronecker]; ring
    rw [this, Complex.mul_re, i1, i2, zero_mul, sub_zero]


theorem x8_inf_mul (S T : Set ℝ) (hS : S.Nonempty) (hT : T.Nonempty) (hS0 : ∀ r ∈ S, 0 ≤ r)
    (hT0 : ∀ r ∈ T, 0 ≤ r) (g : ℝ) (h : ∀ r ∈ S, ∀ r' ∈ T, g ≤ r * r') : g ≤ sInf S * sInf T := by
  have a0 : 0 ≤ sInf S := le_csInf hS hS0
  have step : ∀ r' ∈ T, g ≤ sInf S * r' := by
    intro r' hr'
    rcases (hT0 r' hr').eq_or_lt with h0 | hpos
    · obtain ⟨r, hr⟩ := hS
      have := h r hr r' hr'
      rw [← h0] at this ⊢; simpa using this
    · have : g / r' ≤ sInf S := le_csInf hS fun r hr => (div_le_iff₀ hpos).2 (h r hr r' hr')
      calc g = g / r' * r' := by field_simp
        _ ≤ sInf S * r' := mul_le_mul_of_nonneg_right this hpos.le
  rcases a0.eq_or_lt with h0 | hpos
  · obtain ⟨r', hr'⟩ := hT
    have := step r' hr'
    rw [← h0] at this ⊢; simpa using this
  · have : g / sInf S ≤ sInf T := le_csInf hT fun r' hr' => (div_le_iff₀' hpos).2 (step r' hr')
    calc g = sInf S * (g / sInf S) := by field_simp
      _ ≤ sInf S * sInf T := mul_le_mul_of_nonneg_left this hpos.le

theorem x8_lb (x : ℝ) : logBits (x : EReal) = if x = 0 then ⊥ else ((Real.logb 2 x : ℝ) : EReal) := by
  unfold logBits
  by_cases h : x = 0
  · simp [h]
  · simp [h, EReal.coe_ne_top, EReal.coe_ne_bot]

theorem x8_log (g a b : ℝ) (hg : 0 ≤ g) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : g ≤ a * b) :
    logBits (g : EReal) ≤ logBits (a : EReal) + logBits (b : EReal) := by
  rcases hg.eq_or_lt with h0 | gpos
  · rw [x8_lb, if_pos h0.symm]; exact bot_le
  have apos : 0 < a := by
    rcases ha.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul] at h; linarith
    · exact h0
  have bpos : 0 < b := by
    rcases hb.eq_or_lt with h0 | h0
    · rw [← h0, mul_zero] at h; linarith
    · exact h0
  rw [x8_lb, x8_lb, x8_lb, if_neg gpos.ne', if_neg apos.ne', if_neg bpos.ne', ← EReal.coe_add,
    EReal.coe_le_coe_iff, ← Real.logb_mul apos.ne' bpos.ne']
  exact Real.logb_le_logb_of_le (by norm_num) gpos h

theorem x8_gmul (σ : Matrix (A × B) (A × B) ℂ) (τ : Matrix (C × E) (C × E) ℂ)
    (hσ : σ.IsHermitian) (hτ : τ.IsHermitian) :
    (x8G (bipartiteTensor σ τ)).Nonempty ∧
    sInf (x8G (bipartiteTensor σ τ)) ≤ sInf (x8G σ) * sInf (x8G τ) := by
  have n1 := x8_G_ne σ hσ
  have n2 := x8_G_ne τ hτ
  obtain ⟨r, hr⟩ := n1
  obtain ⟨r', hr'⟩ := n2
  refine ⟨⟨_, x8_prod_mem hr hr'⟩, ?_⟩
  refine x8_inf_mul _ _ ⟨r, hr⟩ ⟨r', hr'⟩ (fun _ h => x8_G_nonneg h) (fun _ h => x8_G_nonneg h) _
    fun a ha b hb => csInf_le ⟨0, fun _ h => x8_G_nonneg h⟩ (x8_prod_mem ha hb)

theorem x8_part1 (σ : Matrix (A × B) (A × B) ℂ) (τ : Matrix (C × E) (C × E) ℂ)
    (hσ : σ.IsHermitian) (hτ : τ.IsHermitian) :
    cGamma (bipartiteTensor σ τ) ≤ cGamma σ + cGamma τ := by
  obtain ⟨n3, hle⟩ := x8_gmul σ τ hσ hτ
  have n1 := x8_G_ne σ hσ
  have n2 := x8_G_ne τ hτ
  unfold cGamma
  rw [x8_cg_eq _ n1, x8_cg_eq _ n2, x8_cg_eq _ n3]
  exact x8_log _ _ _ (le_csInf n3 fun _ h => x8_G_nonneg h) (le_csInf n1 fun _ h => x8_G_nonneg h)
    (le_csInf n2 fun _ h => x8_G_nonneg h) hle

end QAlgorithms.Papers.Independent.Dependency50.P18

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder
open Matrix

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]


local notation "Γ" => QAlgorithms.Papers.Independent.Information100.P04.gamma

def x8P : Matrix ((A × C) × (B × E)) ((A × B) × (C × E)) ℂ := fun i j => if j = x8e i then 1 else 0

def x8eE : (A × C) × (B × E) ≃ (A × B) × (C × E) where
  toFun := x8e
  invFun := fun j => ((j.1.1, j.2.1), (j.1.2, j.2.2))
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem x8_P_apply (Z : Matrix ((A × B) × (C × E)) ((A × B) × (C × E)) ℂ) :
    x8P (A := A) (B := B) (C := C) (E := E) * Z * (x8P (A := A) (B := B) (C := C) (E := E))ᴴ =
      Z.submatrix x8e x8e := by
  ext i j
  simp [x8P, Matrix.mul_apply, conjTranspose_apply]

theorem x8_P_iso : (x8P (A := A) (B := B) (C := C) (E := E))ᴴ * x8P (A := A) (B := B) (C := C) (E := E) = 1 := by
  ext p q
  simp only [x8P, Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply]
  rw [← Equiv.sum_comp (x8eE (A := A) (B := B) (C := C) (E := E)).symm]
  have : ∀ x, x8e ((x8eE (A := A) (B := B) (C := C) (E := E)).symm x) = x := fun x => rfl
  simp [this, eq_comm]

theorem x8_P_channel :
    QAlgorithms.IsChannel (QAlgorithms.conjSuperop (x8P : Matrix ((A × C) × (B × E)) ((A × B) × (C × E)) ℂ)) := by
  refine ⟨1, fun _ => x8P (A := A) (B := B) (C := C) (E := E), ?_, fun ρ => ?_⟩
  · simp [QAlgorithms.IsKrausFamily, x8_P_iso]
  · simp [QAlgorithms.krausApply, QAlgorithms.conjSuperop]

theorem x8_scale_mem {s : Matrix (A × B) (A × B) ℂ} {r t : ℝ} (hr : r ∈ x8G s) (ht : 0 < t) :
    t * r ∈ x8G ((t : ℂ) • s) := by
  obtain ⟨k, l, v, ⟨hk, hl, hv, h1, h2, h3, h4⟩, rfl⟩ := hr
  have ht' : (0 : ℂ) ≤ (t : ℂ) := Complex.zero_le_real.2 ht.le
  have hsm : ∀ X : Matrix (A × B) (A × B) ℂ, Γ ((t : ℂ) • X) = (t : ℂ) • Γ X := fun X => by
    ext i j; rfl
  have hkr : Matrix.kronecker k ((t : ℂ) • l) = (t : ℂ) • Matrix.kronecker k l := by
    simp only [Matrix.kronecker]; rw [kronecker_smul]
  refine ⟨k, (t : ℂ) • l, (t : ℂ) • v, ⟨hk, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [IsHermitian, conjTranspose_smul, hl.eq]
  · simp [IsHermitian, conjTranspose_smul, hv.eq]
  · rw [← smul_add, hsm]; exact h1.smul ht'
  · rw [← smul_sub, hsm]; exact h2.smul ht'
  · rw [hkr, ← smul_add]; exact h3.smul ht'
  · rw [hkr, ← smul_sub]; exact h4.smul ht'
  · rw [hkr, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

theorem x8_fin (D : Divergence) (hD : IsGeneralizedDivergence D)
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    capitalGamma D ρ ≠ ⊤ := by
  obtain ⟨r, hr⟩ := x8_G_ne ρ hρ.1.1
  have r0 := x8_G_nonneg hr
  set t : ℝ := (r + 1)⁻¹
  have tpos : 0 < t := inv_pos.2 (by linarith)
  have hmem := x8_scale_mem hr tpos
  have hle : correlationGauge ((t : ℂ) • ρ) ≤ 1 := by
    refine (x8_cg_le hmem).trans ?_
    rw [show (1 : EReal) = ((1 : ℝ) : EReal) from rfl, EReal.coe_le_coe_iff]
    rw [show t * r = r / (r + 1) by ring]
    rw [div_le_one (by linarith)]; linarith
  have hlt : capitalGamma D ρ < ⊤ := by
    refine lt_of_le_of_lt (sInf_le ⟨(t : ℂ) • ρ, hρ.1.smul (Complex.zero_le_real.2 tpos.le), hle, rfl⟩) ?_
    have key : D ρ ((t : ℂ) • ρ) < ⊤ := by
      rw [hD.scaling ρ ρ t hρ hρ.1 tpos, hD.zeroValue ρ hρ, zero_sub, ← EReal.coe_neg]
      exact EReal.coe_lt_top _
    convert key using 2
  exact hlt.ne

/-- Proposition 8, PDF p.3, (20)–(21), Appendix F p.10.
Only the Gamma clause requires subadditivity of D; the product input is constructed. -/
theorem x8_main (D : Divergence) (hD : IsGeneralizedDivergence D) :
    (∀ (sigma : Matrix (A × B) (A × B) ℂ) (tau : Matrix (C × E) (C × E) ℂ),
      sigma.PosSemidef → tau.PosSemidef →
      cGamma (bipartiteTensor sigma tau) ≤ cGamma sigma + cGamma tau) ∧
    (DivergenceSubadditive D →
      ∀ (sigma : Matrix (A × B) (A × B) ℂ) (tau : Matrix (C × E) (C × E) ℂ),
      QAlgorithms.IsDensityMatrix sigma → QAlgorithms.IsDensityMatrix tau →
      capitalGamma D (bipartiteTensor sigma tau) ≤ capitalGamma D sigma + capitalGamma D tau) := by
  refine ⟨fun σ τ hσ hτ => x8_part1 σ τ hσ.1 hτ.1, fun hsub ρ1 ρ2 h1 h2 => ?_⟩
  refine EReal.le_add_of_forall_gt (Or.inr (x8_fin D hD ρ2 h2)) (Or.inl (x8_fin D hD ρ1 h1)) ?_
  intro a' ha' b' hb'
  obtain ⟨_, ⟨σ, hσ, hγσ, rfl⟩, hx⟩ := sInf_lt_iff.1 ha'
  obtain ⟨_, ⟨τ, hτ, hγτ, rfl⟩, hy⟩ := sInf_lt_iff.1 hb'
  have hγ : correlationGauge (bipartiteTensor σ τ) ≤ 1 := by
    obtain ⟨n3, hle⟩ := x8_gmul σ τ hσ.1 hτ.1
    have n1 := x8_G_ne σ hσ.1
    have n2 := x8_G_ne τ hτ.1
    rw [x8_cg_eq _ n1, show (1 : EReal) = ((1 : ℝ) : EReal) from rfl, EReal.coe_le_coe_iff] at hγσ
    rw [x8_cg_eq _ n2, show (1 : EReal) = ((1 : ℝ) : EReal) from rfl, EReal.coe_le_coe_iff] at hγτ
    rw [x8_cg_eq _ n3, show (1 : EReal) = ((1 : ℝ) : EReal) from rfl, EReal.coe_le_coe_iff]
    exact hle.trans (mul_le_one₀ hγσ (le_csInf n2 fun _ h => x8_G_nonneg h) hγτ)
  have hdens : QAlgorithms.IsDensityMatrix (Matrix.kronecker ρ1 ρ2) := by
    refine ⟨h1.1.kronecker h2.1, ?_⟩
    simp only [Matrix.kronecker]
    rw [trace_kronecker, h1.2, h2.2, mul_one]
  have hdp := hD.dataProcessing _ _ _ hdens (hσ.kronecker hτ) x8_P_channel
  simp only [QAlgorithms.conjSuperop, x8_P_apply] at hdp
  calc capitalGamma D (bipartiteTensor ρ1 ρ2) ≤ D (bipartiteTensor ρ1 ρ2) (bipartiteTensor σ τ) :=
        sInf_le ⟨bipartiteTensor σ τ, x8_bt_psd hσ hτ, hγ, rfl⟩
    _ ≤ D (Matrix.kronecker ρ1 ρ2) (Matrix.kronecker σ τ) := hdp
    _ ≤ D ρ1 σ + D ρ2 τ := hsub ρ1 σ ρ2 τ h1 hσ h2 hτ
    _ ≤ a' + b' := add_le_add hx.le hy.le

end QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Dependency50.P18 in
theorem solution {A B C E : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E]
  (D : Divergence) (hD : IsGeneralizedDivergence D) :
    (∀ (sigma : Matrix (A × B) (A × B) ℂ) (tau : Matrix (C × E) (C × E) ℂ),
      sigma.PosSemidef → tau.PosSemidef →
      cGamma (bipartiteTensor sigma tau) ≤ cGamma sigma + cGamma tau) ∧
    (DivergenceSubadditive D →
      ∀ (sigma : Matrix (A × B) (A × B) ℂ) (tau : Matrix (C × E) (C × E) ℂ),
      QAlgorithms.IsDensityMatrix sigma → QAlgorithms.IsDensityMatrix tau →
      capitalGamma D (bipartiteTensor sigma tau) ≤ capitalGamma D sigma + capitalGamma D tau) :=
  x8_main D hD
