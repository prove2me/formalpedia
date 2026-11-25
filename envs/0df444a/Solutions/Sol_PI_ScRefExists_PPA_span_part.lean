-- Prove2me | solution 1 for PI.ScRefExists.PPA.span_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:58:23.045886+00:00
-- url     : https://prove2.me/submissions/eb3ea908-6492-47b8-930c-0c42c06f6dbb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_NatCastSmulMemL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_SpanSmulInto
import Theorems.Thm_PI_ScRefExists_PPA_GE_star
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_ScRefExists_PPA_span_clear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open PI PI.ScRefExists PI.ScRefExists.PPA
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.PPA
theorem _root_.solution (p m r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M T : ℕ)
    (w wd : Fin (k + 1) → Fin I.n → I.E)
    (hM : Nat.Coprime M p) (hM0 : (M : I.E) ≠ 0) (hT : Nat.Coprime T p) (hT0 : (T : I.E) ≠ 0)
    (hθ1 : GE I (p ^ m) ((θ : I.E) * θ - θ)) (hθ2 : GE I (p ^ m) ((θ : I.E) * star (θ : I.E)))
    (hθ3 : GE I (p ^ m) (1 - (θ : I.E) - star (θ : I.E)))
    (hw : ∀ i, w i ∈ LA I p ∧ wd i ∈ LA I p)
    (hspan : ∀ y ∈ I.L, y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w) ∧
        y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd))
    (Sset : Set (Fin I.n → I.E))
    (hSe : ∀ a, M • e a ∈ Sset) (hSf : ∀ a, M • f a ∈ Sset)
    (hSz : (T : I.E) • ((θ : I.E) • w (Fin.last k) - star (θ : I.E) • wd (Fin.last k)) ∈ Sset)
    (hSb : ∀ i : Fin k, (θ : I.E) • ((T : I.E) • w i.castSucc) ∈ Sset)
    (hSbd : ∀ i : Fin k, star (θ : I.E) • ((T : I.E) • wd i.castSucc) ∈ Sset) :
    ∀ y ∈ I.L, y ∈ Submodule.span (𝓞 I.E) Sset ⊔ gL I (p ^ m) := by
  classical
  set N : Submodule (𝓞 I.E) (Fin I.n → I.E) := Submodule.span (𝓞 I.E) Sset ⊔ gL I (p ^ m) with hN
  have hsm : ∀ (c : 𝓞 I.E) (v : Fin I.n → I.E), c • v = (c : I.E) • v := fun c v => rfl
  have hS : ∀ v ∈ Sset, v ∈ N := fun v hv => Submodule.mem_sup_left (Submodule.subset_span hv)
  have hE : ∀ (c : 𝓞 I.E) (v : Fin I.n → I.E), v ∈ N → (c : I.E) • v ∈ N := fun c v hv => by
    rw [← hsm]
    exact N.smul_mem c hv
  have hnat : ∀ (s : ℕ) (v : Fin I.n → I.E), v ∈ N → (s : I.E) • v ∈ N := fun s v hv => by
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hv s
  have hgl : ∀ x ∈ I.L, ∀ t : 𝓞 I.E, (((p ^ m : ℕ) : I.E) * (t : I.E)) • x ∈ N := by
    intro x hx t
    have h1 : ((p ^ m : ℕ) : I.E) • x ∈ N :=
      Submodule.mem_sup_right (Submodule.subset_span ⟨x, hx, rfl⟩)
    rw [mul_comm, mul_smul]
    exact hE t _ h1
  have hbez : ∀ z ∈ I.L, ∀ s : ℕ, Nat.Coprime s p → (s : I.E) • z ∈ N → z ∈ N := by
    intro z hz s hs hsz
    have hcop : IsCoprime (s : ℤ) ((p ^ m : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_right m hs)
    obtain ⟨u, v, huv⟩ := hcop
    have hpz : ((p ^ m : ℕ) : I.E) • z ∈ N :=
      Submodule.mem_sup_right (Submodule.subset_span ⟨z, hz, rfl⟩)
    have hc : (u : I.E) * (s : I.E) + (v : I.E) * ((p ^ m : ℕ) : I.E) = 1 := by
      have h := congrArg (Int.cast : ℤ → I.E) huv
      push_cast at h ⊢
      linear_combination h
    have e : z = u • ((s : I.E) • z) + v • (((p ^ m : ℕ) : I.E) • z) := by
      rw [← Int.cast_smul_eq_zsmul I.E u, ← Int.cast_smul_eq_zsmul I.E v, smul_smul, smul_smul,
        ← add_smul, hc, one_smul]
    rw [e]
    exact N.add_mem (zsmul_mem hsz u) (zsmul_mem hpz v)
  have hclr : ∀ v ∈ LA I p, ∃ s : ℕ, Nat.Coprime s p ∧ (s : I.E) • v ∈ I.L := by
    intro v hv
    obtain ⟨s, hs, h⟩ := span_clear I p (I.L : Set (Fin I.n → I.E)) hv
    exact ⟨s, hs, by rwa [Submodule.span_eq] at h⟩
  have gen : ∀ (φ φ' : 𝓞 I.E) (u u' : Fin (k + 1) → Fin I.n → I.E),
      (∀ i, u i ∈ LA I p) → (∀ i, u' i ∈ LA I p) →
      (∀ i : Fin k, (φ : I.E) • ((T : I.E) • u i.castSucc) ∈ Sset) →
      (T : I.E) • ((φ : I.E) • u (Fin.last k) - (φ' : I.E) • u' (Fin.last k)) ∈ N →
      GE I (p ^ m) ((φ : I.E) * φ - φ) → GE I (p ^ m) ((φ : I.E) * φ') →
      ∀ y ∈ I.L, y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range u) →
        (φ : I.E) • y ∈ N := by
    intro φ φ' u u' hu hu' hSu hz h1 h2 y hy hyA
    obtain ⟨s2, hs2, hs2L⟩ := hclr _ (hu (Fin.last k))
    obtain ⟨s3, hs3, hs3L⟩ := hclr _ (hu' (Fin.last k))
    obtain ⟨t1, ht1⟩ := h1
    obtain ⟨t2, ht2⟩ := h2
    obtain ⟨s1, hs1, hs1y⟩ := span_clear I p _ hyA
    have key : ∀ v ∈ Submodule.span (𝓞 I.E) (Set.range e ∪ Set.range f ∪ Set.range u),
        ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • v) ∈ N := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        rcases hv with (⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨i, rfl⟩
        · have h := hS _ (hSe a)
          rw [← Nat.cast_smul_eq_nsmul I.E] at h
          have e1 : ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • e a) =
              ((T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • ((M : I.E) • e a)) := by
            simp only [smul_smul]
            congr 1
            push_cast
            ring
          rw [e1]
          exact hnat _ _ (hE φ _ h)
        · have h := hS _ (hSf a)
          rw [← Nat.cast_smul_eq_nsmul I.E] at h
          have e1 : ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • f a) =
              ((T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • ((M : I.E) • f a)) := by
            simp only [smul_smul]
            congr 1
            push_cast
            ring
          rw [e1]
          exact hnat _ _ (hE φ _ h)
        · cases i using Fin.lastCases with
          | last =>
            have hA : ((M * s2 * s3 : ℕ) : I.E) •
                ((φ : I.E) • ((T : I.E) • ((φ : I.E) • u (Fin.last k) - (φ' : I.E) • u' (Fin.last k)))) ∈ N :=
              hnat _ _ (hE φ _ hz)
            have hB : ((M * s3 * T : ℕ) : I.E) • ((((p ^ m : ℕ) : I.E) * (t1 : I.E)) •
                ((s2 : I.E) • u (Fin.last k))) ∈ N := hnat _ _ (hgl _ hs2L t1)
            have hC : ((M * s2 * T : ℕ) : I.E) • ((((p ^ m : ℕ) : I.E) * (t2 : I.E)) •
                ((s3 : I.E) • u' (Fin.last k))) ∈ N := hnat _ _ (hgl _ hs3L t2)
            have e1 : ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • u (Fin.last k)) =
                ((M * s2 * s3 : ℕ) : I.E) •
                  ((φ : I.E) • ((T : I.E) • ((φ : I.E) • u (Fin.last k) - (φ' : I.E) • u' (Fin.last k)))) -
                ((M * s3 * T : ℕ) : I.E) • ((((p ^ m : ℕ) : I.E) * (t1 : I.E)) •
                  ((s2 : I.E) • u (Fin.last k))) +
                ((M * s2 * T : ℕ) : I.E) • ((((p ^ m : ℕ) : I.E) * (t2 : I.E)) •
                  ((s3 : I.E) • u' (Fin.last k))) := by
              rw [← ht1, ← ht2]
              funext i
              simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
              push_cast
              ring
            rw [e1]
            exact N.add_mem (N.sub_mem hA hB) hC
          | cast j =>
            have h := hS _ (hSu j)
            have e1 : ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • u j.castSucc) =
                ((M * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • ((T : I.E) • u j.castSucc)) := by
              simp only [smul_smul]
              congr 1
              push_cast
              ring
            rw [e1]
            exact hnat _ _ h
      | zero => simp
      | add v w _ _ hv hw =>
        rw [smul_add, smul_add]
        exact N.add_mem hv hw
      | smul c v _ hv =>
        rw [hsm, smul_comm (φ : I.E) (c : I.E) v, smul_comm ((M * T * s2 * s3 : ℕ) : I.E) (c : I.E)]
        exact hE c _ hv
    have hk := key _ hs1y
    have hφy : (φ : I.E) • y ∈ I.L := by
      rw [← hsm]
      exact I.L.smul_mem φ hy
    refine hbez _ hφy (M * T * s2 * s3 * s1)
      (Nat.Coprime.mul (Nat.Coprime.mul (Nat.Coprime.mul (Nat.Coprime.mul hM hT) hs2) hs3) hs1) ?_
    have e2 : ((M * T * s2 * s3 * s1 : ℕ) : I.E) • ((φ : I.E) • y) =
        ((M * T * s2 * s3 : ℕ) : I.E) • ((φ : I.E) • ((s1 : I.E) • y)) := by
      simp only [smul_smul]
      congr 1
      push_cast
      ring
    rw [e2]
    exact hk
  obtain ⟨θb, hθb⟩ : ∃ θb : 𝓞 I.E, (θb : I.E) = star (θ : I.E) := by
    have hint : IsIntegral ℤ (starRingEnd I.E (θ : I.E)) := by
      first
      | exact (RingOfIntegers.isIntegral_coe θ).map (starRingEnd I.E).toIntAlgHom
      | exact (θ.2).map (starRingEnd I.E).toIntAlgHom
    exact ⟨⟨starRingEnd I.E (θ : I.E), hint⟩, rfl⟩
  intro y hy
  have hyN1 : (θ : I.E) • y ∈ N :=
    gen θ θb w wd (fun i => (hw i).1) (fun i => (hw i).2) hSb (by rw [hθb]; exact hS _ hSz) hθ1
      (by rw [hθb]; exact hθ2) y hy (hspan y hy).1
  have hz2 : (T : I.E) • ((θb : I.E) • wd (Fin.last k) - (θ : I.E) • w (Fin.last k)) ∈ N := by
    have e : (T : I.E) • ((θb : I.E) • wd (Fin.last k) - (θ : I.E) • w (Fin.last k)) =
        -((T : I.E) • ((θ : I.E) • w (Fin.last k) - star (θ : I.E) • wd (Fin.last k))) := by
      rw [hθb, ← smul_neg, neg_sub]
    rw [e]
    exact N.neg_mem (hS _ hSz)
  have h1' : GE I (p ^ m) ((θb : I.E) * θb - θb) := by
    have h := GE_star I (p ^ m) hθ1
    rwa [star_sub, star_mul', ← hθb] at h
  have h2' : GE I (p ^ m) ((θb : I.E) * θ) := by
    rw [hθb, mul_comm]
    exact hθ2
  have hyN2 : (θb : I.E) • y ∈ N :=
    gen θb θ wd w (fun i => (hw i).2) (fun i => (hw i).1) (fun i => by rw [hθb]; exact hSbd i) hz2 h1' h2'
      y hy (hspan y hy).2
  obtain ⟨t3, ht3⟩ := hθ3
  have h3 : ((1 : I.E) - θ - star (θ : I.E)) • y ∈ N := by
    rw [ht3]
    exact hgl y hy t3
  have e : y = (θ : I.E) • y + (θb : I.E) • y + ((1 : I.E) - θ - star (θ : I.E)) • y := by
    rw [hθb, ← add_smul, ← add_smul,
      show (θ : I.E) + star (θ : I.E) + (1 - θ - star (θ : I.E)) = 1 by ring, one_smul]
  rw [e]
  exact N.add_mem (N.add_mem hyN1 hyN2) h3
end PI.ScRefExists.PPA
