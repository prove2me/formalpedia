-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Generated_proof_7390091ed2be
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:01.654343+00:00
-- url     : https://prove2.me/submissions/99219719-978b-4143-8c63-cf14e9bf9518

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGenerated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace Generated
theorem _root_.solution (hE : Extension.Statement.{u, w, w}) : Generated.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x Q
  obtain ⟨M, hMgam, hMtilde⟩ := hE S Ω N x Ω Q.toSubFamily Q.fg
  obtain ⟨n, deg, gen, hgen, hM⟩ := M.fg
  refine ⟨∑ j, |deg j|, fun c hc I => le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro z hz
    exact (Submodule.mem_iInf _).mp hz I
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  set T := Submodule.span (chartRing S x I) ((Q.twist (twistSys S x c)).secs : Set Ω) with hT

  have hgenT : ∀ (j : Fin n) (f s : Poly S N) (e e' : ℕ), s ∈ monos I.1 → f.IsHomogeneous e' →
      s.IsHomogeneous e → (e' : ℤ) + deg j = e →
      x i ^ c * ((aeval x s)⁻¹ * (aeval x f * gen j)) ∈ T := by
    intro j f s e e' hs hf hse hee
    have hd : deg j ≤ c := (le_abs_self (deg j)).trans
      ((Finset.single_le_sum (fun j _ => abs_nonneg (deg j)) (Finset.mem_univ j)).trans hc)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = c - deg j := ⟨(c - deg j).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hsec : x i ^ k * gen j ∈ (Q.twist (twistSys S x c)).secs := by
      have h1 := M.smul_mem k (deg j) (X i ^ k) (gen j) (isHomogeneous_X_pow i k) (hgen j)
      have h2 : deg j + (k : ℤ) = c := by omega
      rw [h2] at h1
      have h3 := hMgam c h1
      rwa [map_pow, aeval_X, smul_eq_mul] at h3
    have hα : aeval x f / aeval x s ∈ twistMod S x (-deg j) I :=
      Submodule.subset_span ⟨f, s, e, e', hs, hf, hse, by omega, rfl⟩
    rw [twistMod_eq_span (-deg j) I hi, Submodule.mem_span_singleton] at hα
    obtain ⟨b, hb⟩ := hα
    rw [chartRing_smul_def] at hb
    have e1 : x i ^ c * x i ^ (-deg j) = x i ^ k := by
      rw [← zpow_add₀ hxi, ← zpow_natCast, hk]
      congr 1
    have e2 : x i ^ c * ((aeval x s)⁻¹ * (aeval x f * gen j)) = b • (x i ^ k * gen j) := by
      rw [chartRing_smul_def, ← e1]
      calc x i ^ c * ((aeval x s)⁻¹ * (aeval x f * gen j))
          = x i ^ c * (aeval x f / aeval x s) * gen j := by ring
        _ = x i ^ c * ((b : Ω) * x i ^ (-deg j)) * gen j := by rw [hb]
        _ = (b : Ω) * (x i ^ c * x i ^ (-deg j) * gen j) := by ring
    rw [e2]
    exact T.smul_mem b (Submodule.subset_span hsec)

  have key : ∀ y ∈ M.tilde 0 I, x i ^ c * y ∈ T := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => x i ^ c * y ∈ T) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
      refine Submodule.span_induction
        (p := fun m _ => x i ^ c * ((aeval x s)⁻¹ • m) ∈ T) ?_ ?_ ?_ ?_ (hM a hm)
      · rintro _ ⟨j, f, e', hf, hee, rfl⟩
        rw [smul_eq_mul, smul_eq_mul]
        exact hgenT j f s e e' hs hf hse (by omega)
      · rw [smul_zero, mul_zero]; exact T.zero_mem
      · intro m m' _ _ h h'
        rw [smul_add, mul_add]; exact T.add_mem h h'
      · intro r m _ h
        have : x i ^ c * ((aeval x s)⁻¹ • (r • m)) =
            (algebraMap S (chartRing S x I) r) • (x i ^ c * ((aeval x s)⁻¹ • m)) := by
          rw [chartRing_smul_def]
          simp only [smul_eq_mul, Algebra.smul_def]
          change _ = algebraMap S Ω r * _
          ring
        rw [this]; exact T.smul_mem _ h
    · rw [mul_zero]; exact T.zero_mem
    · intro y y' _ _ h h'
      rw [mul_add]; exact T.add_mem h h'
    · intro b y _ h
      have : x i ^ c * (b • y) = b • (x i ^ c * y) := by
        rw [chartRing_smul_def, chartRing_smul_def]; ring
      rw [this]; exact T.smul_mem b h
  change Submodule.span _ _ ≤ T
  rw [Submodule.span_le]
  rintro _ ⟨q, hq, y, hy, rfl⟩
  change q ∈ twistMod S x c I at hq
  rw [twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
  obtain ⟨a, rfl⟩ := hq
  have hy' : y ∈ M.tilde 0 I := by rw [hMtilde I]; exact hy
  have : (a • x i ^ c) • y = a • (x i ^ c * y) := by
    rw [smul_eq_mul, chartRing_smul_def, chartRing_smul_def, mul_assoc]
  rw [SetLike.mem_coe, this]
  exact T.smul_mem a (key y hy')
end Generated
end GroundTheory.Heights₂.Heights.Kleiman
