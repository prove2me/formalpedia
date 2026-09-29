-- Prove2me | solution 1 for PendantArcComplementConnected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T19:58:24.713815+00:00
-- url     : https://prove2.me/submissions/ad70fc3e-dbf9-4603-9d31-01e3e71f2f7e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PolygonalArcFinitePolygonalSetWithVertices
import Theorems.Thm_FinitePolygonalPerturbation
import Theorems.Thm_ArcCrossingEliminationInCollar
import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonallyPathConnected

open Classical
noncomputable section

-- [TABLET NODE: PendantArcComplementConnected]
-- Source: https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PendantArcComplementConnected.lean#L1-L89
theorem solution (K : Set (EuclideanSpace ℝ (Fin 2)))
    (γ : PolygonalArc) :
    IsCompact K →
      PolygonallyPathConnected Kᶜ →
        ((γ.carrier ∩ K = ({γ.source} : Set (EuclideanSpace ℝ (Fin 2))) ∧
            γ.target ∉ K) ∨
          (γ.carrier ∩ K = ({γ.target} : Set (EuclideanSpace ℝ (Fin 2))) ∧
            γ.source ∉ K)) →
          PolygonallyPathConnected (K ∪ γ.carrier)ᶜ := by
  intro hK hKconn hpendant p q hp hq
  have hpKc : p ∈ Kᶜ := by
    intro hpK
    exact hp (Or.inl hpK)
  have hqKc : q ∈ Kᶜ := by
    intro hqK
    exact hq (Or.inl hqK)
  have hpγ : p ∉ γ.carrier := by
    intro hpγ
    exact hp (Or.inr hpγ)
  have hqγ : q ∉ γ.carrier := by
    intro hqγ
    exact hq (Or.inr hqγ)
  obtain ⟨α, hαsource, hαtarget, hαK⟩ := hKconn hpKc hqKc
  obtain ⟨Γ, hΓcarrier, hΓvertices⟩ :=
    PolygonalArcFinitePolygonalSetWithVertices γ
  have hUopen : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hαsourceU : α.source ∈ Kᶜ \ Γ.carrier := by
    constructor
    · simpa [hαsource] using hpKc
    · intro hαΓ
      have hαγ : α.source ∈ γ.carrier := by
        simpa [hΓcarrier] using hαΓ
      exact hpγ (by simpa [hαsource] using hαγ)
  have hαtargetU : α.target ∈ Kᶜ \ Γ.carrier := by
    constructor
    · simpa [hαtarget] using hqKc
    · intro hαΓ
      have hαγ : α.target ∈ γ.carrier := by
        simpa [hΓcarrier] using hαΓ
      exact hqγ (by simpa [hαtarget] using hαγ)
  obtain ⟨α₀, hα₀source, hα₀target, hα₀K, _hα₀near, hα₀gp, _hα₀empty⟩ :=
    FinitePolygonalPerturbation Γ Kᶜ α
      (∅ : Set (EuclideanSpace ℝ (Fin 2))) 1 hUopen hαK hαsourceU hαtargetU
      (by norm_num) isCompact_empty (by simp)
  have hγsource_mem : γ.source ∈ γ.vertices := by
    have h0 : 0 < γ.vertices.length := by
      have hlen := γ.length_ge_two
      omega
    have hsource : γ.vertices[0]'h0 = γ.source := by
      have hhead := γ.source_eq_head
      rw [List.head?_eq_getElem?] at hhead
      rw [List.getElem?_eq_getElem h0] at hhead
      exact Option.some.inj hhead
    rw [← hsource]
    exact List.getElem_mem (l := γ.vertices) (n := 0) h0
  have hγtarget_mem : γ.target ∈ γ.vertices := by
    have hlast_lt : γ.vertices.length - 1 < γ.vertices.length := by
      have hlen := γ.length_ge_two
      omega
    have htarget : γ.vertices[γ.vertices.length - 1]'hlast_lt = γ.target := by
      have hlast := γ.target_eq_last
      rw [List.getLast?_eq_getElem?] at hlast
      rw [List.getElem?_eq_getElem hlast_lt] at hlast
      exact Option.some.inj hlast
    rw [← htarget]
    exact
      List.getElem_mem (l := γ.vertices) (n := γ.vertices.length - 1) hlast_lt
  obtain ⟨β, hβsource, hβtarget, hβcarrier⟩ :=
    ArcCrossingEliminationInCollar K γ Γ α₀ hK hΓcarrier hΓvertices hα₀K
      (by simpa [hα₀source, hαsource] using hp)
      (by simpa [hα₀target, hαtarget] using hq)
      (hα₀gp.2.1 γ.source (hΓvertices γ.source hγsource_mem))
      (hα₀gp.2.1 γ.target (hΓvertices γ.target hγtarget_mem))
      hα₀gp hpendant
  refine ⟨β, ?_, ?_, hβcarrier⟩
  · simpa [hα₀source, hαsource] using hβsource
  · simpa [hα₀target, hαtarget] using hβtarget
