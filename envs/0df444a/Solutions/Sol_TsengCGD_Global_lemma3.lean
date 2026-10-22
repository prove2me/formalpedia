-- Prove2me | solution 1 for TsengCGD.Global.lemma3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T03:57:19.09851+00:00
-- url     : https://prove2.me/submissions/ede1b01d-d051-4a82-a36b-40269323ea37

import Mathlib
import Definitions.Def_TsengCGD_Global_Basic

open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

namespace TsengCGD.Global

lemma g38_lim0 (A B : ℝ) (h : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ A + s * B) : 0 ≤ A := by
  by_contra hA
  push_neg at hA
  set s := min 1 (-A / (2 * (|B| + 1))) with hs
  have hB1 : 0 < |B| + 1 := by positivity
  have hs0 : 0 < s := lt_min one_pos (div_pos (by linarith) (by positivity))
  have hs1 : s ≤ 1 := min_le_left _ _
  have hs2 : s ≤ -A / (2 * (|B| + 1)) := min_le_right _ _
  have h3 : s * (2 * (|B| + 1)) ≤ -A := by
    rwa [le_div_iff₀ (by positivity)] at hs2
  have h4 : s * B ≤ s * |B| := mul_le_mul_of_nonneg_left (le_abs_self B) hs0.le
  have := h s hs0 hs1
  nlinarith

lemma g38_dot_symm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian) (v w : Fin n → ℝ) :
    v ⬝ᵥ (H *ᵥ w) = w ⬝ᵥ (H *ᵥ v) := by
  have hT : Hᵀ = H := by
    have := hH.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hT]

lemma g38_qf_add {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian) (d v : Vec n) (s : ℝ) :
    qf H (d + s • v) = qf H d + 2 * s * (WithLp.ofLp v ⬝ᵥ (H *ᵥ WithLp.ofLp d)) + s ^ 2 * qf H v := by
  have := g38_dot_symm H hH (WithLp.ofLp d) (WithLp.ofLp v)
  simp only [qf, WithLp.ofLp_add, WithLp.ofLp_smul, mulVec_add, mulVec_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul] at *
  rw [this]; ring

lemma g38_qf_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (v : Vec n) :
    qf H (s • v) = s ^ 2 * qf H v := by
  simp only [qf, WithLp.ofLp_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

lemma g38_qf_zero {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : qf H (0 : Vec n) = 0 := by
  simp [qf]

lemma g38_qf_pos {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef) {v : Vec n} (hv : v ≠ 0) :
    0 < qf H v := by
  have h : WithLp.ofLp v ≠ 0 := by
    intro h; apply hv
    have : v = WithLp.toLp 2 (WithLp.ofLp v) := rfl
    rw [this, h]; rfl
  have := hH.dotProduct_mulVec_pos h
  simpa [qf] using this

lemma g38_qf_nonneg {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef) (v : Vec n) :
    0 ≤ qf H v := by
  by_cases hv : v = 0
  · subst hv; simp [qf]
  · exact (g38_qf_pos hH hv).le

lemma g38_qf_cont {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : Continuous (fun v : Vec n => qf H v) := by
  unfold qf
  simp only [dotProduct, mulVec]
  fun_prop

/-- first-order optimality condition for the CGD direction -/
lemma g38_fo {n : ℕ} {f : Vec n → ℝ} {D : Set (Vec n)} {P : Vec n → ℝ} {c : ℝ}
    {H : Matrix (Fin n) (Fin n) ℝ} {x : Vec n} {J : Finset (Fin n)} {d : Vec n}
    (hD : Convex ℝ D) (hPc : ConvexOn ℝ D P) (hc : 0 ≤ c) (hH : H.IsHermitian)
    (hd : IsDir f D P c H x J d) (e : Vec n) (he : SupportedOn J e) (hxe : x + e ∈ D) :
    0 ≤ ⟪gradient f x, e - d⟫ + WithLp.ofLp (e - d) ⬝ᵥ (H *ᵥ WithLp.ofLp d)
      + c * (P (x + e) - P (x + d)) := by
  obtain ⟨hdS, hdD, hdmin⟩ := hd
  apply g38_lim0 _ (qf H (e - d) / 2)
  intro s hs0 hs1
  have hsup : SupportedOn J (d + s • (e - d)) := by
    intro j hj; simp [hdS j hj, he j hj]
  have hmemE : x + (d + s • (e - d)) = (1 - s) • (x + d) + s • (x + e) := by module
  have hmem : x + (d + s • (e - d)) ∈ D := by
    rw [hmemE]; exact hD hdD hxe (by linarith) hs0.le (by ring)
  have h1 := hdmin _ hsup hmem
  have hP := hPc.2 hdD hxe (by linarith : (0:ℝ) ≤ 1 - s) hs0.le (by ring)
  simp only [smul_eq_mul] at hP
  rw [← hmemE] at hP
  simp only [subObj] at h1
  rw [g38_qf_add H hH, inner_add_right, inner_smul_right] at h1
  have h2 : c * P (x + (d + s • (e - d))) ≤ c * ((1 - s) * P (x + d) + s * P (x + e)) :=
    mul_le_mul_of_nonneg_left hP hc
  have h3 : 0 ≤ s * (⟪gradient f x, e - d⟫ + WithLp.ofLp (e - d) ⬝ᵥ (H *ᵥ WithLp.ofLp d)
      + c * (P (x + e) - P (x + d)) + s * (qf H (e - d) / 2)) := by nlinarith
  have := (mul_nonneg_iff_of_pos_left hs0).mp h3; linarith
open Classical in
lemma g38_affine_lb {n : ℕ} {D : Set (Vec n)} {P : Vec n → ℝ}
    (hP : ProxNewton.Inexact.IsProperClosedConvex D P) :
    ∃ A B : ℝ, 0 ≤ A ∧ ∀ y ∈ D, -A * ‖y‖ - B ≤ P y := by
  obtain ⟨⟨x0, hx0⟩, _, hPc, hlsc⟩ := hP
  set Ψ : Vec n → EReal := fun y => if y ∈ D then (P y : EReal) else ⊤ with hΨ
  set S : Set (Vec n × ℝ) := {p | p.1 ∈ D ∧ P p.1 ≤ p.2} with hS
  have hSconv : Convex ℝ S := hPc.convex_epigraph
  have hSclosed : IsClosed S := by
    have h1 := hlsc.isClosed_epigraph
    have e : S = (Prod.map id (fun t : ℝ => (t : EReal))) ⁻¹' {p : Vec n × EReal | Ψ p.1 ≤ p.2} := by
      ext ⟨y, t⟩
      simp only [hS, hΨ, Set.mem_setOf_eq, Set.mem_preimage, Prod.map_apply, id]
      by_cases hy : y ∈ D <;> simp [hy]
    rw [e]
    exact h1.preimage (continuous_id.prodMap continuous_coe_real_ereal)
  have hnot : (x0, P x0 - 1) ∉ S := by simp [hS]
  obtain ⟨f, u, hfu, hS'⟩ := geometric_hahn_banach_point_closed hSconv hSclosed hnot
  have hsplit : ∀ y : Vec n, ∀ t : ℝ, f (y, t) = f (y, 0) + t * f (0, 1) := by
    intro y t
    have : ((y, t) : Vec n × ℝ) = (y, 0) + t • ((0 : Vec n), (1:ℝ)) := by simp
    rw [this, map_add, map_smul, smul_eq_mul]
  set a := f (0, 1) with ha
  have h0 := hS' (x0, P x0) ⟨hx0, le_rfl⟩
  rw [hsplit] at h0 hfu
  have hapos : 0 < a := by nlinarith
  refine ⟨‖f‖ / a, -u / a, by positivity, ?_⟩
  intro y hy
  have h1 := hS' (y, P y) ⟨hy, le_rfl⟩
  rw [hsplit] at h1
  have h2 : f (y, 0) ≤ ‖f‖ * ‖y‖ := by
    have := f.le_opNorm (y, 0)
    have hn : ‖((y, 0) : Vec n × ℝ)‖ = ‖y‖ := by simp
    rw [hn] at this
    exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using this)
  have h3 : -(‖f‖ / a) * ‖y‖ - -u / a = (u - ‖f‖ * ‖y‖) / a := by field_simp; ring
  rw [h3, div_le_iff₀ hapos]
  nlinarith

lemma g38_qf_lower {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) :
    ∃ l > 0, ∀ v : Vec n, l * ‖v‖ ^ 2 ≤ qf H v := by
  have hunit : ∀ v : Vec n, v ≠ 0 → ‖v‖⁻¹ • v ∈ Metric.sphere (0 : Vec n) 1 := by
    intro v hv
    have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
    simp [norm_smul, hnv.ne']
  by_cases hS : (Metric.sphere (0 : Vec n) 1).Nonempty
  · obtain ⟨v0, hv0, hmin⟩ :=
      (isCompact_sphere (0 : Vec n) 1).exists_isMinOn hS (g38_qf_cont H).continuousOn
    have hv0ne : v0 ≠ 0 := by
      intro h; rw [h] at hv0; simp at hv0
    refine ⟨qf H v0, g38_qf_pos hH hv0ne, ?_⟩
    intro v
    by_cases hv : v = 0
    · subst hv; simp [qf]
    · have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have := isMinOn_iff.mp hmin _ (hunit v hv)
      rw [g38_qf_smul] at this
      calc qf H v0 * ‖v‖ ^ 2 ≤ (‖v‖⁻¹) ^ 2 * qf H v * ‖v‖ ^ 2 :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = qf H v := by field_simp
  · refine ⟨1, one_pos, fun v => ?_⟩
    by_cases hv : v = 0
    · subst hv; simp [qf]
    · exact absurd ⟨_, hunit v hv⟩ hS

lemma g38_supp_closed {n : ℕ} (J : Finset (Fin n)) : IsClosed {d : Vec n | SupportedOn J d} := by
  have : {d : Vec n | SupportedOn J d} = ⋂ j ∈ (Jᶜ : Finset (Fin n)), {d : Vec n | d j = 0} := by
    ext d; simp [SupportedOn]
  rw [this]
  exact isClosed_biInter (fun j _ => isClosed_eq (by fun_prop) continuous_const)

open Classical in
lemma g38_exists_dir {n : ℕ} {D : Set (Vec n)} {P : Vec n → ℝ} {c : ℝ}
    (hP : ProxNewton.Inexact.IsProperClosedConvex D P) (hc : 0 < c) {x : Vec n} (hx : x ∈ D)
    (g : Vec n) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) (J : Finset (Fin n)) :
    ∃ d, SupportedOn J d ∧ x + d ∈ D ∧ ∀ d', SupportedOn J d' → x + d' ∈ D →
      ⟪g, d⟫ + qf H d / 2 + c * P (x + d) ≤ ⟪g, d'⟫ + qf H d' / 2 + c * P (x + d') := by
  obtain ⟨A, B, hA, hAB⟩ := g38_affine_lb hP
  obtain ⟨l, hl, hql⟩ := g38_qf_lower H hH
  have hlsc := hP.2.2.2
  set Ψ : Vec n → EReal := fun y => if y ∈ D then (P y : EReal) else ⊤ with hΨ
  set q : Vec n → ℝ := fun d => (⟪g, d⟫ + qf H d / 2) / c with hq
  have hqc : Continuous q := by
    have := g38_qf_cont H
    simp only [hq]; fun_prop
  set Φ : Vec n → EReal := fun d => Ψ (x + d) + (q d : EReal) with hΦ
  have hΦl : LowerSemicontinuous Φ := by
    apply LowerSemicontinuous.add'
    · exact hlsc.comp (continuous_const.add continuous_id)
    · exact (continuous_coe_real_ereal.comp hqc).lowerSemicontinuous
    · intro d
      apply EReal.continuousAt_add
      · right; simp
      · right; simp
  have hΦin : ∀ d, x + d ∈ D → Φ d = ((P (x + d) + q d : ℝ) : EReal) := by
    intro d hd; simp [hΦ, hΨ, hd]
  have hΦout : ∀ d, x + d ∉ D → Φ d = ⊤ := by
    intro d hd; simp [hΦ, hΨ, hd]
  set K := Φ ⁻¹' Set.Iic (Φ 0) ∩ {d : Vec n | SupportedOn J d} with hK
  have hKc : IsClosed K := (hΦl.isClosed_preimage _).inter (g38_supp_closed J)
  have h0D : x + 0 ∈ D := by simpa using hx
  have hΦ0 : Φ 0 = ((P x : ℝ) : EReal) := by rw [hΦin 0 h0D]; simp [hq, g38_qf_zero]
  have hKD : ∀ d ∈ K, x + d ∈ D ∧ P (x + d) + q d ≤ P x := by
    intro d hd
    have hd1 := hd.1
    simp only [Set.mem_preimage, Set.mem_Iic, hΦ0] at hd1
    by_cases hdD : x + d ∈ D
    · rw [hΦin d hdD] at hd1
      exact ⟨hdD, EReal.coe_le_coe_iff.mp hd1⟩
    · rw [hΦout d hdD] at hd1; simp at hd1
  set b := ‖g‖ + c * A with hb
  set M := c * (P x + A * ‖x‖ + B) with hM
  set R := 2 * (b + |M| + 1) / l + 1 with hR
  have hKb : K ⊆ Metric.closedBall 0 R := by
    intro d hd
    obtain ⟨hdD, hle⟩ := hKD d hd
    have h1 := hAB _ hdD
    have h2 : ‖x + d‖ ≤ ‖x‖ + ‖d‖ := norm_add_le _ _
    have h3 : -‖g‖ * ‖d‖ ≤ ⟪g, d⟫ := by
      have := abs_real_inner_le_norm g d
      have := neg_abs_le ⟪g, d⟫
      nlinarith
    have h4 : q d * c = ⟪g, d⟫ + qf H d / 2 := by simp only [hq]; field_simp
    have hqd := hql d
    have h5 : l * ‖d‖ ^ 2 / 2 - b * ‖d‖ ≤ M := by
      have hcle := mul_le_mul_of_nonneg_left hle hc.le
      have hAd := mul_le_mul_of_nonneg_left h2 hA
      have : c * (-A * ‖x + d‖ - B) ≤ c * P (x + d) := mul_le_mul_of_nonneg_left h1 hc.le
      simp only [hb, hM]
      nlinarith
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hcon
    push_neg at hcon
    have hb0 : 0 ≤ b := by positivity
    have hM' : M ≤ |M| := le_abs_self M
    have ht : 0 ≤ ‖d‖ := norm_nonneg d
    have hR1 : 1 ≤ R := by
      have : 0 ≤ 2 * (b + |M| + 1) / l := by positivity
      simp only [hR]; linarith
    have hlR : l * R / 2 - b ≥ |M| + 1 := by
      simp only [hR]; field_simp; nlinarith [abs_nonneg M]
    have h6 : l * ‖d‖ / 2 - b ≥ |M| + 1 := by nlinarith
    have h7 : ‖d‖ * (l * ‖d‖ / 2 - b) ≥ 1 * (|M| + 1) :=
      mul_le_mul (by linarith) h6 (by positivity) (by linarith)
    nlinarith [abs_nonneg M]
  have hKcomp : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded hKc (Metric.isBounded_closedBall.subset hKb)
  have h0K : (0 : Vec n) ∈ K := ⟨by simp, fun j _ => by simp⟩
  obtain ⟨dstar, hdK, hmin⟩ := (hΦl.lowerSemicontinuousOn K).exists_isMinOn ⟨0, h0K⟩ hKcomp
  obtain ⟨hdD, _⟩ := hKD dstar hdK
  refine ⟨dstar, hdK.2, hdD, ?_⟩
  intro d' hd's hd'
  have hle : Φ dstar ≤ Φ d' := by
    by_cases hd'K : d' ∈ K
    · exact hmin hd'K
    · have h1 : Φ dstar ≤ Φ 0 := hdK.1
      have : ¬ Φ d' ≤ Φ 0 := fun h => hd'K ⟨h, hd's⟩
      exact le_trans h1 (not_le.mp this).le
  rw [hΦin _ hdD, hΦin _ hd', EReal.coe_le_coe_iff] at hle
  have e1 : q dstar * c = ⟪g, dstar⟫ + qf H dstar / 2 := by simp only [hq]; field_simp
  have e2 : q d' * c = ⟪g, d'⟫ + qf H d' / 2 := by simp only [hq]; field_simp
  have := mul_le_mul_of_nonneg_left hle hc.le
  nlinarith

lemma g38_dH_spec {n : ℕ} {f : Vec n → ℝ} {D : Set (Vec n)} {P : Vec n → ℝ} {c : ℝ}
    (hs : Standing f D P c) {x : Vec n} (hx : x ∈ D) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (J : Finset (Fin n)) :
    IsDir f D P c H x J (dH f D P c H x J) := by
  obtain ⟨d, hdS, hdD, hmin⟩ := g38_exists_dir hs.properConvexLsc hs.c_pos hx (gradient f x) H hH J
  exact Classical.epsilon_spec ⟨d, hdS, hdD, fun d' h1 h2 => by simpa [subObj] using hmin d' h1 h2⟩


/-! ## Lemma 3 -/

def l3bil {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x y : Vec n) : ℝ :=
  WithLp.ofLp x ⬝ᵥ (M *ᵥ WithLp.ofLp y)

section bil
variable {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℝ) (x y z : Vec n) (s : ℝ)

lemma l3_qf_eq : qf M x = l3bil M x x := rfl
lemma l3_add_l : l3bil M (x + y) z = l3bil M x z + l3bil M y z := by
  simp [l3bil, add_dotProduct]
lemma l3_add_r : l3bil M x (y + z) = l3bil M x y + l3bil M x z := by
  simp [l3bil, mulVec_add, dotProduct_add]
lemma l3_sub_l : l3bil M (x - y) z = l3bil M x z - l3bil M y z := by
  simp [l3bil, sub_dotProduct]
lemma l3_sub_r : l3bil M x (y - z) = l3bil M x y - l3bil M x z := by
  simp [l3bil, mulVec_sub, dotProduct_sub]
lemma l3_smul_l : l3bil M (s • x) y = s * l3bil M x y := by
  simp [l3bil, smul_dotProduct]
lemma l3_smul_r : l3bil M x (s • y) = s * l3bil M x y := by
  simp [l3bil, mulVec_smul, dotProduct_smul]
lemma l3_madd : l3bil (M + N) x y = l3bil M x y + l3bil N x y := by
  simp [l3bil, add_mulVec, dotProduct_add]
lemma l3_msub : l3bil (M - N) x y = l3bil M x y - l3bil N x y := by
  simp [l3bil, sub_mulVec, dotProduct_sub]
lemma l3_zero_r : l3bil M x 0 = 0 := by simp [l3bil]
end bil

lemma l3_symm {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) (x y : Vec n) :
    l3bil M x y = l3bil M y x := g38_dot_symm M hM _ _

lemma l3_supp_add {n : ℕ} {J : Finset (Fin n)} {x y : Vec n} (hx : SupportedOn J x)
    (hy : SupportedOn J y) : SupportedOn J (x + y) := by
  intro j hj; simp [hx j hj, hy j hj]
lemma l3_supp_sub {n : ℕ} {J : Finset (Fin n)} {x y : Vec n} (hx : SupportedOn J x)
    (hy : SupportedOn J y) : SupportedOn J (x - y) := by
  intro j hj; simp [hx j hj, hy j hj]
lemma l3_supp_smul {n : ℕ} {J : Finset (Fin n)} {x : Vec n} (s : ℝ) (hx : SupportedOn J x) :
    SupportedOn J (s • x) := by
  intro j hj; simp [hx j hj]

lemma l3_cs {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef) (x y : Vec n) :
    l3bil M x y ^ 2 ≤ qf M x * qf M y := by
  by_cases hy : y = 0
  · subst hy; simp [l3_zero_r, g38_qf_zero]
  have hqy := g38_qf_pos hM hy
  have key := g38_qf_nonneg hM (x + (-(l3bil M x y) / qf M y) • y)
  simp only [l3_qf_eq, l3_add_l, l3_add_r, l3_smul_l, l3_smul_r] at key
  rw [l3_symm hM.1 y x] at key
  rw [l3_qf_eq, l3_qf_eq]
  set B := l3bil M x y
  set qy := l3bil M y y
  set qx := l3bil M x x
  have hqy' : qy ≠ 0 := hqy.ne'
  have e : qx + -B / qy * B + -B / qy * (B + -B / qy * qy) = qx - B ^ 2 / qy := by
    field_simp; ring
  rw [e] at key
  have := (div_le_iff₀ hqy).mp (by linarith : B ^ 2 / qy ≤ qx)
  exact this

lemma l3_le_of_sq {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith

lemma l3_polar {n : ℕ} {C A : Matrix (Fin n) (Fin n) ℝ} (hC : C.IsHermitian) (hA : A.IsHermitian)
    {J : Finset (Fin n)} {κ : ℝ} (hκ : 0 ≤ κ)
    (hb : ∀ x, SupportedOn J x → |qf C x| ≤ κ * qf A x) {z b : Vec n}
    (hz : SupportedOn J z) (hbS : SupportedOn J b)
    (h : qf A z ≤ l3bil C z b / 2) : qf A z ≤ κ ^ 2 * qf A b / 4 := by
  have key : ∀ μ : ℝ, 4 * μ * l3bil C z b ≤ 2 * κ * (μ ^ 2 * qf A z + qf A b) := by
    intro μ
    have h1 := hb (μ • z + b) (l3_supp_add (l3_supp_smul μ hz) hbS)
    have h2 := hb (μ • z - b) (l3_supp_sub (l3_supp_smul μ hz) hbS)
    have e1 : qf C (μ • z + b) = μ ^ 2 * qf C z + 2 * μ * l3bil C z b + qf C b := by
      simp only [l3_qf_eq, l3_add_l, l3_add_r, l3_smul_l, l3_smul_r]
      rw [l3_symm hC b z]; ring
    have e2 : qf C (μ • z - b) = μ ^ 2 * qf C z - 2 * μ * l3bil C z b + qf C b := by
      simp only [l3_qf_eq, l3_sub_l, l3_sub_r, l3_smul_l, l3_smul_r]
      rw [l3_symm hC b z]; ring
    have e3 : κ * qf A (μ • z + b) + κ * qf A (μ • z - b) =
        2 * κ * (μ ^ 2 * qf A z + qf A b) := by
      simp only [l3_qf_eq, l3_add_l, l3_add_r, l3_sub_l, l3_sub_r, l3_smul_l, l3_smul_r]
      rw [l3_symm hA b z]; ring
    have := le_abs_self (qf C (μ • z + b))
    have := neg_abs_le (qf C (μ • z - b))
    linarith
  rcases hκ.lt_or_eq with hκ | hκ
  · have k := key (2 / κ)
    have e1 : 4 * (2 / κ) * l3bil C z b = (8 * l3bil C z b) / κ := by field_simp; ring
    have e2 : 2 * κ * ((2 / κ) ^ 2 * qf A z + qf A b) = (8 * qf A z + 2 * κ ^ 2 * qf A b) / κ := by
      field_simp; ring
    rw [e1, e2, div_le_div_iff_of_pos_right hκ] at k
    linarith
  · subst hκ
    have k := key 1
    nlinarith

/-- Rayleigh-type sets are compact images of the unit sphere of the coordinate subspace. -/
lemma l3_K_compact {n : ℕ} (J : Finset (Fin n)) :
    IsCompact ({u : Vec n | SupportedOn J u} ∩ Metric.sphere 0 1) :=
  (isCompact_sphere (0 : Vec n) 1).inter_left (g38_supp_closed J)

lemma l3_K_ne {n : ℕ} {J : Finset (Fin n)} (hJ : J.Nonempty) :
    ({u : Vec n | SupportedOn J u} ∩ Metric.sphere 0 1).Nonempty := by
  obtain ⟨j, hj⟩ := hJ
  refine ⟨EuclideanSpace.single j 1, ?_, by simp⟩
  intro i hi
  have : i ≠ j := fun h => hi (h ▸ hj)
  simp [EuclideanSpace.single_apply, this]

lemma l3_set_eq {n : ℕ} (J : Finset (Fin n)) (F : Vec n → ℝ)
    (hF : ∀ (s : ℝ) (u : Vec n), s ≠ 0 → F (s • u) = F u) :
    {r | ∃ u : Vec n, SupportedOn J u ∧ u ≠ 0 ∧ r = F u} =
      F '' ({u : Vec n | SupportedOn J u} ∩ Metric.sphere 0 1) := by
  ext r
  constructor
  · rintro ⟨u, hu, hu0, rfl⟩
    have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    refine ⟨‖u‖⁻¹ • u, ⟨l3_supp_smul _ hu, ?_⟩, hF _ _ (inv_ne_zero hn.ne')⟩
    simp [norm_smul, hn.ne']
  · rintro ⟨u, ⟨hu, hu1⟩, rfl⟩
    refine ⟨u, hu, ?_, rfl⟩
    intro h; rw [h] at hu1; simp at hu1

lemma l3_compact {n : ℕ} (J : Finset (Fin n)) (F : Vec n → ℝ)
    (hF : ∀ (s : ℝ) (u : Vec n), s ≠ 0 → F (s • u) = F u)
    (hc : ContinuousOn F ({u : Vec n | SupportedOn J u} ∩ Metric.sphere 0 1)) :
    IsCompact {r | ∃ u : Vec n, SupportedOn J u ∧ u ≠ 0 ∧ r = F u} := by
  rw [l3_set_eq J F hF]; exact (l3_K_compact J).image_of_continuousOn hc

lemma l3_set_ne {n : ℕ} {J : Finset (Fin n)} (hJ : J.Nonempty) (F : Vec n → ℝ) :
    {r | ∃ u : Vec n, SupportedOn J u ∧ u ≠ 0 ∧ r = F u}.Nonempty := by
  obtain ⟨u, hu, hu1⟩ := l3_K_ne hJ
  refine ⟨F u, u, hu, ?_, rfl⟩
  intro h; rw [h] at hu1; simp at hu1

lemma l3_ray_compact {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (J : Finset (Fin n)) :
    IsCompact {r | ∃ u : Vec n, SupportedOn J u ∧ u ≠ 0 ∧ r = qf A u / ‖u‖ ^ 2} := by
  apply l3_compact J (fun u => qf A u / ‖u‖ ^ 2)
  · intro s u hs
    simp only [g38_qf_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [mul_div_mul_left _ _ (pow_ne_zero 2 hs)]
  · apply (g38_qf_cont A).continuousOn.div ((continuous_norm.pow 2).continuousOn)
    rintro u ⟨_, hu⟩
    have : ‖u‖ = 1 := by simpa using hu
    simp [this]

lemma l3_gen_compact {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef)
    (Ht : Matrix (Fin n) (Fin n) ℝ) (J : Finset (Fin n)) :
    IsCompact {r | ∃ u : Vec n, SupportedOn J u ∧ u ≠ 0 ∧ r = qf Ht u / qf H u} := by
  apply l3_compact J (fun u => qf Ht u / qf H u)
  · intro s u hs
    simp only [g38_qf_smul]
    rw [mul_div_mul_left _ _ (pow_ne_zero 2 hs)]
  · apply (g38_qf_cont Ht).continuousOn.div (g38_qf_cont H).continuousOn
    rintro u ⟨_, hu⟩
    have hu0 : u ≠ 0 := by intro h; rw [h] at hu; simp at hu
    exact (g38_qf_pos hH hu0).ne'

lemma l3_ray_bounds {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {J : Finset (Fin n)} (hJ : J.Nonempty)
    {u : Vec n} (hu : SupportedOn J u) :
    lamMin A J * ‖u‖ ^ 2 ≤ qf A u ∧ qf A u ≤ lamMax A J * ‖u‖ ^ 2 := by
  by_cases hu0 : u = 0
  · subst hu0; simp [g38_qf_zero]
  have hn : 0 < ‖u‖ ^ 2 := by have := norm_pos_iff.mpr hu0; positivity
  have hS := l3_ray_compact A J
  have hr : qf A u / ‖u‖ ^ 2 ∈ {r | ∃ u : Vec n, SupportedOn J u ∧ u ≠ 0 ∧ r = qf A u / ‖u‖ ^ 2} :=
    ⟨u, hu, hu0, rfl⟩
  have h1 : lamMin A J ≤ qf A u / ‖u‖ ^ 2 := csInf_le hS.bddBelow hr
  have h2 : qf A u / ‖u‖ ^ 2 ≤ lamMax A J := le_csSup hS.bddAbove hr
  constructor
  · rwa [le_div_iff₀ hn] at h1
  · rwa [div_le_iff₀ hn] at h2

lemma l3_lamMin_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {J : Finset (Fin n)} (hJ : J.Nonempty)
    (hpos : ∀ u : Vec n, SupportedOn J u → u ≠ 0 → 0 < qf A u) : 0 < lamMin A J := by
  have hS := l3_ray_compact A J
  obtain ⟨u, hu, hu0, he⟩ := hS.sInf_mem (l3_set_ne hJ _)
  show 0 < sInf {r | ∃ u : Vec n, SupportedOn J u ∧ u ≠ 0 ∧ r = qf A u / ‖u‖ ^ 2}
  rw [he]
  have := norm_pos_iff.mpr hu0
  exact div_pos (hpos u hu hu0) (by positivity)

lemma l3_gen_bounds {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef)
    (Ht : Matrix (Fin n) (Fin n) ℝ) {J : Finset (Fin n)} {u : Vec n} (hu : SupportedOn J u) :
    genMin H Ht J * qf H u ≤ qf Ht u ∧ qf Ht u ≤ genMax H Ht J * qf H u := by
  by_cases hu0 : u = 0
  · subst hu0; simp [g38_qf_zero]
  have hq := g38_qf_pos hH hu0
  have hS := l3_gen_compact hH Ht J
  have hr : qf Ht u / qf H u ∈ {r | ∃ u : Vec n, SupportedOn J u ∧ u ≠ 0 ∧ r = qf Ht u / qf H u} :=
    ⟨u, hu, hu0, rfl⟩
  have h1 : genMin H Ht J ≤ qf Ht u / qf H u := csInf_le hS.bddBelow hr
  have h2 : qf Ht u / qf H u ≤ genMax H Ht J := le_csSup hS.bddAbove hr
  constructor
  · rwa [le_div_iff₀ hq] at h1
  · rwa [div_le_iff₀ hq] at h2

lemma l3_genMin_nonneg {n : ℕ} {H Ht : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef) (hHt : Ht.PosDef)
    {J : Finset (Fin n)} (hJ : J.Nonempty) : 0 ≤ genMin H Ht J := by
  have hS := l3_gen_compact hH Ht J
  obtain ⟨u, hu, hu0, he⟩ := hS.sInf_mem (l3_set_ne hJ _)
  show 0 ≤ sInf {r | ∃ u : Vec n, SupportedOn J u ∧ u ≠ 0 ∧ r = qf Ht u / qf H u}
  rw [he]
  exact (div_pos (g38_qf_pos hHt hu0) (g38_qf_pos hH hu0)).le

lemma l3_gen_le {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef)
    (Ht : Matrix (Fin n) (Fin n) ℝ) {J : Finset (Fin n)} (hJ : J.Nonempty) :
    genMin H Ht J ≤ genMax H Ht J := by
  have hS := l3_gen_compact hH Ht J
  exact csInf_le_csSup (l3_set_ne hJ _) hS.bddBelow hS.bddAbove

lemma l3_inner_toLp {n : ℕ} (v : Fin n → ℝ) (z : Vec n) :
    ⟪(WithLp.toLp 2 v : Vec n), z⟫ = WithLp.ofLp z ⬝ᵥ v := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

lemma l3_zero_two (L K : ℝ) (h : ∀ t : ℝ, 0 ≤ t * L + t ^ 2 * K) : L = 0 := by
  have h1 : 0 ≤ L := by
    apply g38_lim0 L K
    intro s hs _
    have := h s
    have e : s * L + s ^ 2 * K = s * (L + s * K) := by ring
    rw [e] at this
    exact (mul_nonneg_iff_of_pos_left hs).mp this
  have h2 : 0 ≤ -L := by
    apply g38_lim0 (-L) K
    intro s hs _
    have := h (-s)
    have e : -s * L + (-s) ^ 2 * K = s * (-L + s * K) := by ring
    rw [e] at this
    exact (mul_nonneg_iff_of_pos_left hs).mp this
  linarith

open Classical in
lemma l3_univ_pcc {n : ℕ} :
    ProxNewton.Inexact.IsProperClosedConvex (Set.univ : Set (Vec n)) (fun _ => 0) := by
  refine ⟨Set.univ_nonempty, convex_univ, convexOn_const 0 convex_univ, ?_⟩
  simp only [Set.mem_univ, if_true]
  exact lowerSemicontinuous_const

/-- the representing vector `w` of `z ↦ ((H + Ht) b)ᵀ z / 2` on the coordinate subspace -/
lemma l3_rep {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef)
    (Ht : Matrix (Fin n) (Fin n) ℝ) (J : Finset (Fin n)) (b : Vec n) :
    ∃ w, SupportedOn J w ∧ ∀ z, SupportedOn J z →
      l3bil H z w = (l3bil H z b + l3bil Ht z b) / 2 := by
  set g : Vec n := -((1 / 2 : ℝ) • (WithLp.toLp 2 ((H + Ht) *ᵥ WithLp.ofLp b) : Vec n)) with hg
  have hgz : ∀ z : Vec n, ⟪g, z⟫ = -(1 / 2) * (l3bil H z b + l3bil Ht z b) := by
    intro z
    rw [hg, inner_neg_left, inner_smul_left, l3_inner_toLp, ← l3_madd]
    simp [l3bil]
  obtain ⟨w, hwS, -, hmin⟩ := g38_exists_dir (l3_univ_pcc (n := n)) one_pos (x := 0)
    (Set.mem_univ _) g H hH J
  refine ⟨w, hwS, fun z hz => ?_⟩
  have key : ∀ t : ℝ, 0 ≤ t * (⟪g, z⟫ + l3bil H z w) + t ^ 2 * (qf H z / 2) := by
    intro t
    have := hmin (w + t • z) (l3_supp_add hwS (l3_supp_smul t hz)) (Set.mem_univ _)
    simp only [mul_zero, add_zero] at this
    rw [inner_add_right, inner_smul_right] at this
    simp only [l3_qf_eq, l3_add_l, l3_add_r, l3_smul_l, l3_smul_r] at this ⊢
    rw [l3_symm hH.1 w z] at this
    nlinarith
  have := l3_zero_two _ _ key
  rw [hgz] at this
  linarith

theorem lemma3_aux {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (x : Vec n) (J : Finset (Fin n)) (hJ : J.Nonempty)
    (H Ht : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) (hHt : Ht.PosDef)
    (a b : Vec n) (hda : IsDir f D P c H x J a) (hdb : IsDir f D P c Ht x J b) :
    ‖b‖ ≤
      ((1 + genMax H Ht J +
        Real.sqrt (1 - 2 * genMin H Ht J + (genMax H Ht J) ^ 2)) / 2) *
        (lamMax H J / lamMin Ht J) * ‖a‖ ∧
    ((∀ u : Vec n, SupportedOn J u → u ≠ 0 → qf Ht u < qf H u) →
      ‖a‖ ≤ Real.sqrt (lamMax (H - Ht) J / lamMin (H - Ht) J) * ‖b‖) := by
  have haS : SupportedOn J a := hda.1
  have hbS : SupportedOn J b := hdb.1
  have hD := hs.properConvexLsc.2.1
  have hPc := hs.properConvexLsc.2.2.1
  have hc := hs.c_pos.le
  -- basic inequality
  have fo1 := g38_fo hD hPc hc hH.1 hda b hbS hdb.2.1
  have fo2 := g38_fo hD hPc hc hHt.1 hdb a haS hda.2.1
  have hBI : qf Ht b + qf H a ≤ l3bil H a b + l3bil Ht a b := by
    have e1 : WithLp.ofLp (b - a) ⬝ᵥ (H *ᵥ WithLp.ofLp a) = l3bil H b a - l3bil H a a := by
      rw [← l3_sub_l]; rfl
    have e2 : WithLp.ofLp (a - b) ⬝ᵥ (Ht *ᵥ WithLp.ofLp b) = l3bil Ht a b - l3bil Ht b b := by
      rw [← l3_sub_l]; rfl
    rw [e1] at fo1; rw [e2] at fo2
    rw [inner_sub_right] at fo1 fo2
    rw [l3_symm hH.1 b a] at fo1
    simp only [l3_qf_eq]
    linarith
  have hHa := g38_qf_nonneg hH a
  have hHb := g38_qf_nonneg hH b
  refine ⟨?_, ?_⟩
  · -- first bound
    set gM := genMax H Ht J
    set gm := genMin H Ht J
    set σ := Real.sqrt (1 - 2 * gm + gM ^ 2)
    have hgm0 : 0 ≤ gm := l3_genMin_nonneg hH hHt hJ
    have hgle : gm ≤ gM := l3_gen_le hH Ht hJ
    have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
    have hσ1 : 1 - gm ≤ σ := by
      apply Real.le_sqrt_of_sq_le; nlinarith
    have hσ2 : gM - 1 ≤ σ := by
      apply Real.le_sqrt_of_sq_le; nlinarith
    obtain ⟨w, hwS, hrep⟩ := l3_rep hH Ht J b
    -- bound on ‖w‖_H
    have hw1 : qf H w ≤ (1 + gM) ^ 2 * qf H b / 4 := by
      apply l3_polar (C := H + Ht) (hH.1.add hHt.1) hH.1 (by linarith) _ hwS hbS
      · rw [l3_madd, l3_qf_eq H w, hrep w hwS]
      · intro y hy
        have hq1 := g38_qf_nonneg hH y
        have hq2 := g38_qf_nonneg hHt y
        have hg := (l3_gen_bounds hH Ht hy).2
        have e : qf (H + Ht) y = qf H y + qf Ht y := by simp only [l3_qf_eq, l3_madd]
        rw [e, abs_of_nonneg (by linarith)]
        nlinarith
    -- bound on ‖b - w‖_H
    have hw2 : qf H (b - w) ≤ σ ^ 2 * qf H b / 4 := by
      apply l3_polar (C := H - Ht) (hH.1.sub hHt.1) hH.1 hσ0 _ (l3_supp_sub hbS hwS) hbS
      · have h1 := hrep (b - w) (l3_supp_sub hbS hwS)
        have e : qf H (b - w) = l3bil H (b - w) b - l3bil H (b - w) w := by
          rw [l3_qf_eq, l3_sub_r]
        rw [l3_msub, e, h1]; linarith
      · intro y hy
        have hq1 := g38_qf_nonneg hH y
        have hg := l3_gen_bounds hH Ht hy
        have e : qf (H - Ht) y = qf H y - qf Ht y := by simp only [l3_qf_eq, l3_msub]
        rw [e, abs_le]
        constructor <;> nlinarith
    -- identities
    have hb_w : l3bil H b w = (qf H b + qf Ht b) / 2 := hrep b hbS
    have ha_w : l3bil H a w = (l3bil H a b + l3bil Ht a b) / 2 := hrep a haS
    have iden1 : qf H (b - w) = qf H w - qf Ht b := by
      simp only [l3_qf_eq, l3_sub_l, l3_sub_r] at hb_w ⊢
      rw [l3_symm hH.1 w b]; linarith
    have iden2 : qf H (w - a) = qf H w - (2 * l3bil H a w - qf H a) := by
      simp only [l3_qf_eq, l3_sub_l, l3_sub_r]
      rw [l3_symm hH.1 w a]; ring
    have hT : qf Ht b ≤ l3bil H a w + l3bil H a (w - a) := by
      rw [l3_sub_r, ← l3_qf_eq]; linarith
    -- square roots
    set ta := Real.sqrt (qf H a)
    set tb := Real.sqrt (qf H b)
    set tw := Real.sqrt (qf H w)
    set te := Real.sqrt (qf H (w - a))
    have hwa0 := g38_qf_nonneg hH (w - a)
    have hw0 := g38_qf_nonneg hH w
    have hta : ta ^ 2 = qf H a := Real.sq_sqrt hHa
    have htb : tb ^ 2 = qf H b := Real.sq_sqrt hHb
    have htw : tw ^ 2 = qf H w := Real.sq_sqrt hw0
    have hte : te ^ 2 = qf H (w - a) := Real.sq_sqrt hwa0
    have ta0 : 0 ≤ ta := Real.sqrt_nonneg _
    have tb0 : 0 ≤ tb := Real.sqrt_nonneg _
    have tw0 : 0 ≤ tw := Real.sqrt_nonneg _
    have te0 : 0 ≤ te := Real.sqrt_nonneg _
    have c1 : l3bil H a w ≤ ta * tw := by
      apply l3_le_of_sq (by positivity)
      rw [mul_pow, hta, htw]; exact l3_cs hH a w
    have c2 : l3bil H a (w - a) ≤ ta * te := by
      apply l3_le_of_sq (by positivity)
      rw [mul_pow, hte, hta]; exact l3_cs hH a (w - a)
    have b1 : tw ≤ (1 + gM) / 2 * tb := by
      have hgM0 : 0 ≤ gM := le_trans hgm0 hgle
      apply l3_le_of_sq (by positivity)
      rw [htw, mul_pow, htb]
      have e : ((1 + gM) / 2) ^ 2 * qf H b = (1 + gM) ^ 2 * qf H b / 4 := by ring
      rw [e]; exact hw1
    have b2 : te ≤ σ / 2 * tb := by
      apply l3_le_of_sq (by positivity)
      rw [hte, mul_pow, htb]
      have : qf H (w - a) ≤ qf H (b - w) := by rw [iden1, iden2]; linarith
      have e : (σ / 2) ^ 2 * qf H b = σ ^ 2 * qf H b / 4 := by ring
      rw [e]; linarith
    set ρ := (1 + gM + σ) / 2
    have hρ0 : 0 ≤ ρ := by
      have : 0 ≤ gM := le_trans hgm0 hgle
      show 0 ≤ (1 + gM + σ) / 2; linarith
    have hm : qf Ht b ≤ ρ * ta * tb := by
      have h1 := mul_le_mul_of_nonneg_left b1 ta0
      have h2 := mul_le_mul_of_nonneg_left b2 ta0
      have e : ta * ((1 + gM) / 2 * tb) + ta * (σ / 2 * tb) = ρ * ta * tb := by
        show _ = (1 + gM + σ) / 2 * ta * tb; ring
      linarith
    -- Rayleigh bounds
    have rHa := (l3_ray_bounds H hJ haS).2
    have rHb := (l3_ray_bounds H hJ hbS).2
    have rHtb := (l3_ray_bounds Ht hJ hbS).1
    have hlt : 0 < lamMin Ht J := l3_lamMin_pos Ht hJ (fun u _ hu => g38_qf_pos hHt hu)
    have hlH : 0 < lamMin H J := l3_lamMin_pos H hJ (fun u _ hu => g38_qf_pos hH hu)
    have hLH : 0 ≤ lamMax H J := by
      have := (l3_ray_bounds H hJ haS)
      obtain ⟨j, hj⟩ := hJ
      have hsj : SupportedOn J (EuclideanSpace.single j (1:ℝ) : Vec n) := by
        intro i hi
        have : i ≠ j := fun h => hi (h ▸ hj)
        simp [EuclideanSpace.single_apply, this]
      have h1 := l3_ray_bounds H ⟨j, hj⟩ hsj
      have hn : ‖(EuclideanSpace.single j (1:ℝ) : Vec n)‖ = 1 := by simp
      rw [hn] at h1
      linarith
    set L := lamMax H J
    have hta' : ta ≤ Real.sqrt L * ‖a‖ := by
      apply l3_le_of_sq (by positivity)
      rw [hta, mul_pow, Real.sq_sqrt hLH]; exact rHa
    have htb' : tb ≤ Real.sqrt L * ‖b‖ := by
      apply l3_le_of_sq (by positivity)
      rw [htb, mul_pow, Real.sq_sqrt hLH]; exact rHb
    have hsL : Real.sqrt L ^ 2 = L := Real.sq_sqrt hLH
    have hsL0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
    have hfin : lamMin Ht J * ‖b‖ ^ 2 ≤ ρ * L * ‖a‖ * ‖b‖ := by
      have h1 : ta * tb ≤ (Real.sqrt L * ‖a‖) * (Real.sqrt L * ‖b‖) :=
        mul_le_mul hta' htb' tb0 (by positivity)
      have h2 : (Real.sqrt L * ‖a‖) * (Real.sqrt L * ‖b‖) = L * ‖a‖ * ‖b‖ := by
        calc (Real.sqrt L * ‖a‖) * (Real.sqrt L * ‖b‖) = Real.sqrt L ^ 2 * ‖a‖ * ‖b‖ := by ring
          _ = L * ‖a‖ * ‖b‖ := by rw [hsL]
      have h3 : ρ * (ta * tb) ≤ ρ * (L * ‖a‖ * ‖b‖) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hρ0
      have e1 : ρ * (ta * tb) = ρ * ta * tb := by ring
      have e2 : ρ * (L * ‖a‖ * ‖b‖) = ρ * L * ‖a‖ * ‖b‖ := by ring
      linarith
    show ‖b‖ ≤ ρ * (L / lamMin Ht J) * ‖a‖
    by_cases hb0 : ‖b‖ = 0
    · rw [hb0]; have := norm_nonneg a; positivity
    have hbpos : 0 < ‖b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hb0)
    have h4 : lamMin Ht J * ‖b‖ ≤ ρ * L * ‖a‖ := by
      have : lamMin Ht J * ‖b‖ * ‖b‖ ≤ ρ * L * ‖a‖ * ‖b‖ := by
        calc lamMin Ht J * ‖b‖ * ‖b‖ = lamMin Ht J * ‖b‖ ^ 2 := by ring
          _ ≤ _ := hfin
      exact le_of_mul_le_mul_right this hbpos
    rw [show ρ * (L / lamMin Ht J) * ‖a‖ = ρ * L * ‖a‖ / lamMin Ht J by field_simp]
    rw [le_div_iff₀ hlt]; linarith
  · -- second bound
    intro hlt
    have hMs : (H - Ht).IsHermitian := hH.1.sub hHt.1
    have hMpos : ∀ u : Vec n, SupportedOn J u → u ≠ 0 → 0 < qf (H - Ht) u := by
      intro u hu hu0
      have := hlt u hu hu0
      have e : qf (H - Ht) u = qf H u - qf Ht u := by simp only [l3_qf_eq, l3_msub]
      rw [e]; linarith
    have hab := l3_supp_sub haS hbS
    have hq_ab : 0 ≤ qf (H - Ht) (a - b) := by
      by_cases h0 : a - b = 0
      · rw [h0, g38_qf_zero]
      · exact (hMpos _ hab h0).le
    have hHt_ab := g38_qf_nonneg hHt (a - b)
    have hMa_le : qf (H - Ht) a ≤ l3bil (H - Ht) a b := by
      have e : qf Ht (a - b) = qf Ht a - 2 * l3bil Ht a b + qf Ht b := by
        simp only [l3_qf_eq, l3_sub_l, l3_sub_r]; rw [l3_symm hHt.1 b a]; ring
      simp only [l3_qf_eq, l3_msub] at hBI e hHt_ab ⊢
      linarith
    have hMab : qf (H - Ht) (a - b) = qf (H - Ht) a - 2 * l3bil (H - Ht) a b + qf (H - Ht) b := by
      simp only [l3_qf_eq, l3_sub_l, l3_sub_r]; rw [l3_symm hMs b a]; ring
    have hMa_b : qf (H - Ht) a ≤ qf (H - Ht) b := by linarith
    have r1 := (l3_ray_bounds (H - Ht) hJ haS).1
    have r2 := (l3_ray_bounds (H - Ht) hJ hbS).2
    have hl := l3_lamMin_pos (H - Ht) hJ hMpos
    have hsq : ‖a‖ ^ 2 ≤ lamMax (H - Ht) J / lamMin (H - Ht) J * ‖b‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl]
      calc ‖a‖ ^ 2 * lamMin (H - Ht) J = lamMin (H - Ht) J * ‖a‖ ^ 2 := by ring
        _ ≤ _ := by linarith
    rw [← Real.sqrt_sq (norm_nonneg b), ← Real.sqrt_mul' _ (sq_nonneg _)]
    exact Real.le_sqrt_of_sq_le hsq

theorem lemma3_core {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (x : Vec n) (hx : x ∈ D) (J : Finset (Fin n)) (hJ : J.Nonempty)
    (H Ht : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) (hHt : Ht.PosDef) :
    let d := dH f D P c H x J
    let dt := dH f D P c Ht x J
    ‖dt‖ ≤
      ((1 + genMax H Ht J +
        Real.sqrt (1 - 2 * genMin H Ht J + (genMax H Ht J) ^ 2)) / 2) *
        (lamMax H J / lamMin Ht J) * ‖d‖ ∧
    ((∀ u : Vec n, SupportedOn J u → u ≠ 0 → qf Ht u < qf H u) →
      ‖d‖ ≤ Real.sqrt (lamMax (H - Ht) J / lamMin (H - Ht) J) * ‖dt‖) :=
  lemma3_aux f D P c hs x J hJ H Ht hH hHt _ _ (g38_dH_spec hs hx H hH J) (g38_dH_spec hs hx Ht hHt J)

end TsengCGD.Global

open TsengCGD.Global


theorem solution {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (x : Vec n) (hx : x ∈ D) (J : Finset (Fin n)) (hJ : J.Nonempty)
    (H Ht : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) (hHt : Ht.PosDef) :
    let d := dH f D P c H x J
    let dt := dH f D P c Ht x J
    ‖dt‖ ≤
      ((1 + genMax H Ht J +
        Real.sqrt (1 - 2 * genMin H Ht J + (genMax H Ht J) ^ 2)) / 2) *
        (lamMax H J / lamMin Ht J) * ‖d‖ ∧
    ((∀ u : Vec n, SupportedOn J u → u ≠ 0 → qf Ht u < qf H u) →
      ‖d‖ ≤ Real.sqrt (lamMax (H - Ht) J / lamMin (H - Ht) J) * ‖dt‖) := by
  exact lemma3_core f D P c hs x hx J hJ H Ht hH hHt
