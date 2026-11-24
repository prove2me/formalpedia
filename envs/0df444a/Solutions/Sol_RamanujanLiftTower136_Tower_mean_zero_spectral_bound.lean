-- Prove2me | solution 1 for RamanujanLiftTower136.Tower.mean_zero_spectral_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T12:51:17.817907+00:00
-- url     : https://prove2.me/submissions/70940fca-c28e-4550-8b74-109b27551b64
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_RamanujanLiftTower136_Tower_adjacency_is_hecke
import Theorems.Thm_RamanujanLiftTower136_Tower_level_order_is_eichler
import Theorems.Thm_RamanujanLiftTower136_Tower_norm_class_functions_constant
import Theorems.Thm_RamanujanLiftTower136_Tower_hecke_eigenvalue_ramanujan_bound

open RamanujanLiftTower136.Tower

/-- Proposition 5.1, reduced to: Proposition 4.2 (adjacency is the Hecke operator), the Eichler
level of `E_n`, the Jacquet–Langlands/Ramanujan–Petersson eigenvalue bound for the Hecke
operator on the class set, and constancy of the functions factoring through the reduced norm. -/
theorem solution (p n : ℕ) (hp : admissible p) (hn : 1 ≤ n)
    (lambda : ℂ) (h : Vertex n → ℂ) (hne : h ≠ 0)
    (hzero : ∑ t, h t = 0) (heigen : ∀ t, adjacency p n h t = lambda*h t) :
    ‖lambda‖ ≤ 2 * Real.sqrt p := by
  classical
  obtain ⟨hbij, -, hhecke⟩ := adjacency_is_hecke p n hp hn
  have hinj : ∀ s t : Vertex n, vertexClass n s = vertexClass n t → s = t :=
    fun s t hst => hbij.injOn (Set.mem_univ s) (Set.mem_univ t) hst
  -- transport `h` to a function on ideal classes along the bijection `t ↦ [I_t]`
  obtain ⟨h', hdef⟩ : ∃ h' : IdealClass → ℂ, ∀ c, h' c =
      if hc : ∃ t : Vertex n, vertexClass n t = c then h hc.choose else 0 :=
    ⟨_, fun _ => rfl⟩
  have hh' : ∀ t : Vertex n, h' (vertexClass n t) = h t := by
    intro t
    have hex : ∃ s : Vertex n, vertexClass n s = vertexClass n t := ⟨t, rfl⟩
    rw [hdef, dif_pos hex]
    exact congrArg h (hinj _ _ hex.choose_spec)
  have hcomp : (fun s => h' (vertexClass n s)) = h := funext hh'
  -- `h'` is an eigenfunction of the Hecke operator on the whole class set
  have heig' : ∀ c ∈ classSet (levelOrder n),
      hecke p (levelOrder n) h' c = lambda * h' c := by
    intro c hc
    obtain ⟨t, -, rfl⟩ := hbij.surjOn hc
    calc hecke p (levelOrder n) h' (vertexClass n t)
        = adjacency p n (fun s => h' (vertexClass n s)) t := (hhecke h' t).symm
      _ = adjacency p n h t := by rw [hcomp]
      _ = lambda * h t := heigen t
      _ = lambda * h' (vertexClass n t) := by rw [hh' t]
  rcases hecke_eigenvalue_ramanujan_bound p (n+2) hp (levelOrder n)
      (level_order_is_eichler n) lambda h' heig' with hb | hf
  · exact hb
  · -- the exceptional case: `h` is constant, hence zero because its sum vanishes
    exfalso
    apply hne
    have hconst : ∀ s t : Vertex n, h s = h t := by
      intro s t
      rw [← hh' s, ← hh' t]
      exact norm_class_functions_constant n h' hf _ _
        (hbij.mapsTo (Set.mem_univ s)) (hbij.mapsTo (Set.mem_univ t))
    funext t
    have h2 : (∑ s, h s) = ∑ _s : Vertex n, h t :=
      Finset.sum_congr rfl (fun s _ => hconst s t)
    have hz : (∑ _s : Vertex n, h t) = 0 := h2.symm.trans hzero
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hz
    have hcard : (Fintype.card (Vertex n) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simpa using (mul_eq_zero.mp hz).resolve_left hcard
